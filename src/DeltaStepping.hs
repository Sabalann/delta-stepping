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
    :: Bool                             -- Whether to print intermediate states to the console, for debugging purposes
    -> Graph                            -- graph to analyse
    -> Distance                         -- delta (step width, bucket width)
    -> Node                             -- index of the starting node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
  threadCount <- getNumCapabilities             -- the number of (kernel) threads to use: the 'x' in '+RTS -Nx'

  -- Initialise the algorithm
  (buckets, distances)  <- initialise graph delta source
  printVerbose verbose "initialse" graph delta buckets distances

  let
    -- The algorithm loops while there are still non-empty buckets
    loop = do
      done <- allBucketsEmpty buckets
      if done
      then return ()
      else do
        printVerbose verbose "result" graph delta buckets distances
        step verbose threadCount graph delta buckets distances
        loop
  loop

  printVerbose verbose "result" graph delta buckets distances
  -- Once the tentative distances are finalised, convert into an immutable array
  -- to prevent further updates. It is safe to use this "unsafe" function here
  -- because the mutable vector will not be used any more, so referential
  -- transparency is preserved for the frozen immutable vector.
  --
  -- NOTE: The function 'Data.Vector.convert' can be used to translate between
  -- different (compatible) vector types (e.g. boxed to storable)
  --
  M.unsafeFreeze distances

-- Initialise algorithm state
--
initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph _ source = do
    -- Create the distances vector and initialize to infinity
    let numNodes = G.order graph
    distances <- M.replicate numNodes infinity
    M.write distances source 0 -- Distance to the source is 0

    -- Create the bucket array (cyclic buckets)
    let bucketCount = numNodes `div` 10 + 1 -- Arbitrary choice for bucket count
    bucketArray <- V.replicate bucketCount Set.empty

    -- Add the source node to the first bucket
    V.modify bucketArray (Set.insert source) 0

    -- Initialize the firstBucket reference
    firstBucket <- newIORef 0

    -- Return the initial state
    return (Buckets { firstBucket = firstBucket, bucketArray = bucketArray }, distances)



-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.
--
step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets distances = do
    -- Find the smallest non-empty bucket
    bucketIndex <- findNextBucket buckets

    -- Read and clear the current bucket
    currentBucket <- V.read (bucketArray buckets) (bucketIndex `mod` V.length (bucketArray buckets))
    V.write (bucketArray buckets) (bucketIndex `mod` V.length (bucketArray buckets)) Set.empty

    -- Relax light edges
    let lightPredicate = (<= delta)
    lightRequests <- findRequests threadCount lightPredicate graph currentBucket distances
    relaxRequests threadCount buckets distances delta lightRequests

    -- Relax heavy edges
    let heavyPredicate = (> delta)
    heavyRequests <- findRequests threadCount heavyPredicate graph currentBucket distances
    relaxRequests threadCount buckets distances delta heavyRequests

    -- Update the first bucket index if necessary
    updateFirstBucketIndex buckets

    -- Print the verbose output, if enabled
    when verbose $ printCurrentBucket graph delta buckets distances


updateFirstBucketIndex :: Buckets -> IO ()
updateFirstBucketIndex Buckets { firstBucket = firstBucket, bucketArray = bucketArray } = do
    let bucketCount = V.length bucketArray -- Pure length calculation
    forM_ [0 .. bucketCount - 1] $ \i -> do
        bucket <- V.read bucketArray i
        unless (Set.null bucket) $ writeIORef firstBucket i




-- Once all buckets are empty, the tentative distances are finalised and the
-- algorithm terminates.
--
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty Buckets { firstBucket = firstBucket, bucketArray = bucketArray } = do
    -- Read through the bucket array
    bucketList <- mapM (V.read bucketArray) [0 .. V.length bucketArray - 1]
    -- Check if all IntSets are empty
    return $ all Set.null bucketList



-- Return the index of the smallest on-empty bucket. Assumes that there is at
-- least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int
findNextBucket Buckets { firstBucket = firstBucket, bucketArray = bucketArray } = do
    start <- readIORef firstBucket
    let bucketCount = V.length bucketArray
    let indices = [start .. start + bucketCount - 1] -- Cyclic indices
    -- Find the first non-empty bucket
    let findIndex [] = error "No non-empty buckets found!" -- Safety check
        findIndex (i:is) = do
            bucket <- V.read bucketArray (i `mod` bucketCount)
            if Set.null bucket
                then findIndex is
                else return i
    findIndex indices



-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: Int
    -> (Distance -> Bool)
    -> Graph
    -> IntSet
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests threadCount p graph v' distances = do
    -- Initialize an empty MVar to store the requests map
    requestsVar <- newMVar Map.empty

    -- Convert the set of nodes to a list for processing
    let nodes = Set.toList v'

    -- Fork threads to process nodes in parallel
    forkThreads threadCount $ \threadId -> do
        -- Each thread processes a chunk of nodes
        forM_ (chunk threadCount threadId nodes) $ \node -> do
            -- Get the current distance for this node
            currentDist <- M.read distances node
            -- Get outgoing edges and filter by predicate
            let edges = G.out graph node
            let filteredEdges = [(w, currentDist + d) | (_, w, d) <- edges, p d]
            -- Update the requests map with the new tentative distances
            modifyMVar_ requestsVar $ \requests ->
                return $ foldr (\(w, newDist) -> Map.insertWith min w newDist) requests filteredEdges

    -- Return the accumulated requests map
    readMVar requestsVar
  where
    -- Helper function to split work among threads
    chunk n t xs = [x | (i, x) <- zip [0 ..] xs, i `mod` n == t]


-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Int
    -> Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> IO ()
relaxRequests threadCount buckets distances delta req = do
    -- Convert the IntMap of requests into a list of (node, distance) pairs
    let requests = Map.toList req

    -- Process requests in parallel
    forkThreads threadCount $ \threadId -> do
        -- Each thread processes a chunk of requests
        forM_ (chunk threadCount threadId requests) $ \(node, newDistance) ->
            relax buckets distances delta (node, newDistance)
  where
    -- Helper function to split work among threads
    chunk n t xs = [x | (i, x) <- zip [0 ..] xs, i `mod` n == t]


-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax :: Buckets
      -> TentativeDistances
      -> Distance
      -> (Node, Distance) -- (node, newDistance)
      -> IO ()
relax Buckets { firstBucket = firstBucket, bucketArray = bucketArray } distances delta (node, newDistance) = do
    -- Read the current distance of the node
    currentDistance <- M.read distances node

    -- Check if the new distance is smaller
    when (newDistance < currentDistance) $ do
        -- Update the tentative distance
        M.write distances node newDistance

        -- Compute the new bucket index
        let newBucketIndex = floor (newDistance / delta)

        -- Remove the node from its current bucket (if applicable)
        let currentBucketIndex = floor (currentDistance / delta)
        when (not $ isInfinite currentDistance) $ do
            V.modify bucketArray (Set.delete node) (currentBucketIndex `mod` V.length bucketArray)

        -- Add the node to the new bucket
        V.modify bucketArray (Set.insert node) (newBucketIndex `mod` V.length bucketArray)



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

