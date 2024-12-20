{-# LANGUAGE RecordWildCards  #-}
--
-- INFOB3CC Concurrency
-- Practical 2: Single Source Shortest Path
--
--    Δ-stepping: A parallelisable shortest path algorithm
--    https://www.sciencedirect.com/science/article/pii/S0196677403000762
--
-- https://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--



module DeltaStepping (

  Graph, Node, Distance,
  deltaStepping,

) where

import Sample
import Utils

import Control.Concurrent
import Control.Concurrent.MVar
import Control.Monad
import Data.Bits
import Data.Graph.Inductive                                         ( Gr )
import Data.IORef
import Data.IntMap.Strict                                           ( IntMap )
import Data.IntSet                                                  ( IntSet )
import Data.Vector.Storable                                         ( Vector )
import Data.Word
import Foreign.Ptr
import Foreign.Storable
import Text.Printf
import qualified Data.Graph.Inductive                               as G
import qualified Data.IntMap.Strict                                 as Map
import qualified Data.IntSet                                        as Set
import qualified Data.Vector.Mutable                                as V
import qualified Data.Vector.Storable                               as M ( unsafeFreeze )
import qualified Data.Vector.Storable.Mutable                       as M


type Graph    = Gr String Distance  -- Graphs have nodes labelled with Strings and edges labelled with their distance
type Node     = Int                 -- Nodes (vertices) in the graph are integers in the range [0..]
type Distance = Float               -- Distances between nodes are (positive) floating point values


-- | Find the length of the shortest path from the given node to all other nodes
-- in the graph. If the destination is not reachable from the starting node the
-- distance is 'Infinity'.
--
-- Nodes must be numbered [0..]
--
-- Negative edge weights are not supported.
--
-- NOTE: The type of the 'deltaStepping' function should not change (since that
-- is what the test suite expects), but you are free to change the types of all
-- other functions and data structures in this module as you require.
--
deltaStepping
    :: Bool
    -> Graph
    -> Distance
    -> Node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
    threadCount <- getNumCapabilities
    (buckets, distances) <- initialise graph delta source
    printVerbose verbose "initialise" graph delta buckets distances

    let loop :: Int -> IO ()
        loop stepCount = do
            done <- allBucketsEmpty buckets
            if done
                then return ()
                else do
                    step verbose threadCount graph delta buckets distances
                    loop (stepCount + 1)

    loop 0
    printVerbose verbose "result" graph delta buckets distances
    M.unsafeFreeze distances


initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph _ source = do
    -- Create the distances vector and initialize to infinity
    let numNodes = G.order graph
    distances <- M.replicate numNodes infinity
    M.write distances source 0

    -- Create the bucket array (cyclic buckets)
    let bucketCount = numNodes `div` 10 + 1
    bucketArray <- V.replicate bucketCount Set.empty

    -- Adding the source node to the first bucket
    V.modify bucketArray (Set.insert source) 0

    firstBucket <- newIORef 0

    return (Buckets { firstBucket = firstBucket, bucketArray = bucketArray }, distances)



-- Take a single step of the algorithm.
-- Specifically we perform one iteration of the outer while loop.

step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets distances = do
    bucketIndex <- findNextBucket buckets

    -- Read and clear the current bucket
    currentBucket <- V.read (bucketArray buckets) (bucketIndex `mod` V.length (bucketArray buckets))
    V.write (bucketArray buckets) (bucketIndex `mod` V.length (bucketArray buckets)) Set.empty

    -- Relax the light edges
    let lightPredicate = (<= delta)
    lightRequests <- findRequests threadCount lightPredicate graph currentBucket distances
    relaxRequests threadCount buckets distances delta lightRequests

    -- Relax the heavy edges
    let heavyPredicate = (> delta)
    heavyRequests <- findRequests threadCount heavyPredicate graph currentBucket distances
    relaxRequests threadCount buckets distances delta heavyRequests

    updateFirstBucketIndex buckets

    when verbose $ printCurrentBucket graph delta buckets distances


updateFirstBucketIndex :: Buckets -> IO ()
updateFirstBucketIndex Buckets{firstBucket = firstBucket, bucketArray = bucketArray} = do
    bucketCount <- pure $ V.length bucketArray
    start <- readIORef firstBucket
    let loop i
          | i == start + bucketCount = return ()
          | otherwise = do
              bucket <- V.read bucketArray (i `mod` bucketCount)
              if Set.null bucket
                  then loop (i + 1)
                  else writeIORef firstBucket (i `mod` bucketCount)
    loop start





-- When all the buckets are empty, the tentative distances are confirmed, and the
-- algorithm will terminate.

allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty Buckets { firstBucket = firstBucket, bucketArray = bucketArray } = do
    bucketList <- mapM (V.read bucketArray) [0 .. V.length bucketArray - 1]
    return $ all Set.null bucketList



-- Gives the index of the smallest non-empty bucket. 
-- Assumes that there is at least one non-empty bucket remaining.

findNextBucket :: Buckets -> IO Int
findNextBucket Buckets { firstBucket = firstBucket, bucketArray = bucketArray } = do
    start <- readIORef firstBucket
    let bucketCount = V.length bucketArray
    let idxs = [start .. start + bucketCount - 1] 
    -- Finding the first non-empty bucket
    let findIndex [] = error "No non-empty buckets found!" 
        findIndex (i:is) = do
            bucket <- V.read bucketArray (i `mod` bucketCount)
            if Set.null bucket
                then findIndex is
                else return i
    findIndex idxs



-- Creating requests of (node, distance) pairs that fulfil the given predicate

findRequests
    :: Int
    -> (Distance -> Bool)
    -> Graph
    -> IntSet
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests threadCount p graph currentBucket distances = do
    requestsVar <- newMVar Map.empty
    let nodes = Set.toList currentBucket

    forkThreads threadCount $ \threadId -> do
        localRequests <- newIORef Map.empty
        forM_ (chunk threadCount threadId nodes) $ \node -> do
            currentDist <- M.read distances node
            let edges = G.out graph node
            let filteredEdges = [(w, currentDist + d) | (_, w, d) <- edges, p d]
            modifyIORef' localRequests $ \reqs ->
                foldr (\(w, newDist) -> Map.insertWith min w newDist) reqs filteredEdges
        -- Merge local requests into the global map
        localReqs <- readIORef localRequests
        atomicallyUpdate requestsVar (Map.toList localReqs)



    readMVar requestsVar
  where
    atomicallyUpdate var updates = modifyMVar_ var $ \requests ->
        return $ foldr (\(w, newDist) -> Map.insertWith min w newDist) requests updates





-- Process the requests for each of the provided (node, distance) pairs.

relaxRequests
    :: Int
    -> Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> IO ()
relaxRequests threadCount Buckets { bucketArray = bucketArray, firstBucket = firstBucket } distances delta req = do
    let requests = Map.toList req

    forkThreads threadCount $ \threadId -> do
        forM_ (chunk threadCount threadId requests) $ \(node, newDistance) -> do
            currentDistance <- M.read distances node

            -- Only update if the new distance is smaller
            when (newDistance < currentDistance) $ do
                M.write distances node newDistance

                let newBucketIdx = floor (newDistance / delta)
                let currentBucketIdx = floor (currentDistance / delta)

                when (not $ isInfinite currentDistance) $
                    V.modify bucketArray (Set.delete node) (currentBucketIdx `mod` V.length bucketArray)

                V.modify bucketArray (Set.insert node) (newBucketIdx `mod` V.length bucketArray)




--Perform a single relaxation, placing the given node in the appropriate bucket.

relax
    :: Buckets
    -> TentativeDistances
    -> Distance
    -> (Node, Distance)
    -> IO ()
relax Buckets { firstBucket = firstBucket, bucketArray = bucketArray } distances delta (node, newDistance) = do
    currentDistance <- M.read distances node

    -- Only update if the new distance is smaller
    when (newDistance < currentDistance) $ do
        M.write distances node newDistance
        let newBucketIdx = floor (newDistance / delta)
        let currentBucketIdx = floor (currentDistance / delta)

        when (not $ isInfinite currentDistance) $
            V.modify bucketArray (Set.delete node) (currentBucketIdx `mod` V.length bucketArray)

        V.modify bucketArray (Set.insert node) (newBucketIdx `mod` V.length bucketArray)




-- Split a list into chunks for each thread
chunk :: Int -> Int -> [a] -> [a]
chunk n t xs = [x | (i, x) <- zip [0 ..] xs, i `mod` n == t]


-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------
--
-- Here are a collection of (data)types and utility functions that you can use.
-- You are free to change these as necessary.
--

type TentativeDistances = M.IOVector Distance

data Buckets = Buckets
  { firstBucket   :: {-# UNPACK #-} !(IORef Int)           -- real index of the first bucket (j)
  , bucketArray   :: {-# UNPACK #-} !(V.IOVector IntSet)   -- cyclic array of buckets
  }


-- The initial tentative distance, or the distance to unreachable nodes
--
infinity :: Distance
infinity = 1/0


-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n action = do
  -- Fork the threads and create a list of the MVars which per thread tell
  -- whether the action has finished.
  finishVars <- mapM work [0 .. n - 1]
  -- Once all the worker threads have been launched, now wait for them all to
  -- finish by blocking on their signal MVars.
  mapM_ takeMVar finishVars
  where
    -- Create a new empty MVar that is shared between the main (spawning) thread
    -- and the worker (child) thread. The main thread returns immediately after
    -- spawning the worker thread. Once the child thread has finished executing
    -- the given action, it fills in the MVar to signal to the calling thread
    -- that it has completed.
    --
    work :: Int -> IO (MVar ())
    work index = do
      done <- newEmptyMVar
      _    <- forkOn index (action index >> putMVar done ())  -- pin the worker to a given CPU core
      return done


printVerbose :: Bool -> String -> Graph -> Distance -> Buckets -> TentativeDistances -> IO ()
printVerbose verbose title graph delta buckets distances = when verbose $ do
  putStrLn $ "# " ++ title
  printCurrentState graph distances
  printBuckets graph delta buckets distances
  putStrLn "Press enter to continue"
  _ <- getLine
  return ()

-- Print the current state of the algorithm (tentative distance to all nodes)
--
printCurrentState
    :: Graph
    -> TentativeDistances
    -> IO ()
printCurrentState graph distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+------------\n"
  forM_ (G.labNodes graph) $ \(v, l) -> do
    x <- M.read distances v
    if isInfinite x
       then printf "  %4d  |  %5v  |  -\n" v l
       else printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

printBuckets
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printBuckets graph delta Buckets{..} distances = do
  first <- readIORef firstBucket
  mapM_
    (\idx -> do
      let idx' = first + idx
      printf "Bucket %d: [%f, %f)\n" idx' (fromIntegral idx' * delta) ((fromIntegral idx'+1) * delta)
      b <- V.read bucketArray (idx' `rem` V.length bucketArray)
      printBucket graph b distances
    )
    [ 0 .. V.length bucketArray - 1 ]

-- Print the current bucket
--
printCurrentBucket
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printCurrentBucket graph delta Buckets{..} distances = do
  j <- readIORef firstBucket
  b <- V.read bucketArray (j `rem` V.length bucketArray)
  printf "Bucket %d: [%f, %f)\n" j (fromIntegral j * delta) (fromIntegral (j+1) * delta)
  printBucket graph b distances

-- Print a given bucket
--
printBucket
    :: Graph
    -> IntSet
    -> TentativeDistances
    -> IO ()
printBucket graph bucket distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+-----------\n"
  forM_ (Set.toAscList bucket) $ \v -> do
    let ml = G.lab graph v
    x <- M.read distances v
    case ml of
      Nothing -> printf "  %4d  |   -   |  %f\n" v x
      Just l  -> printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

