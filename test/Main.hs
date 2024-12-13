{-# LANGUAGE NumericUnderscores #-}

module Main where

import Sample
import DeltaStepping

import Test.Similar
import qualified Test.Gen                                           as Gen

import Data.Vector.Storable                                         ( Vector )
import Hedgehog
import Test.Tasty                                                   hiding ( defaultMain )
import Test.Tasty.Bench
import Test.Tasty.Hedgehog
import Test.Tasty.Runners
import qualified Data.Graph.Inductive                               as G
import qualified Data.Vector.Generic                                as V
import qualified Hedgehog.Gen                                       as Gen
import qualified Hedgehog.Internal.Gen                              as Gen
import qualified Hedgehog.Internal.Seed                             as Seed
import qualified Hedgehog.Internal.Tree                             as Tree
import qualified Hedgehog.Range                                     as Range
import Control.Monad

import GHC.Conc                                                     ( setNumCapabilities )
import GHC.Stack

main :: IO ()
main = defaultMain
  [ localOption (NumThreads 1)                            -- run each test sequentially with many cores
  $ localOption (mkTimeout 60_000_000)                    -- timeout each test after 60 s
  $ localOption (HedgehogTestLimit (Just 1000))           -- number of each test to run
  $ localOption (HedgehogShrinkLimit (Just 100))          -- number of shrinks allowed while searching for minimal reproducible test case
  $ localOption (HedgehogDiscardLimit (Just 1000))        -- maximum number of discard cases before a test fails
  $ testGroup "test"
      [ testProperty "sample1"   $ propSample sample1 3
      , testProperty "sample2"   $ propSample sample2 3
      , testProperty "line"      $ propArbitrary (Gen.line (Range.linear 2 Gen._MAX_NODES) Gen.enumerated Gen.distance) 0.7
      , testProperty "loop"      $ propArbitrary (Gen.loop (Range.linear 2 Gen._MAX_NODES) Gen.enumerated Gen.distance) 0.7
      , testProperty "arbitrary" $ propArbitrary (Gen.arbitrary (Range.linear 1 Gen._MAX_NODES) (Range.linear 1 Gen._MAX_EDGES) Gen.enumerated Gen.distance) 0.7
      , localOption (HedgehogTestLimit (Just 1))
      $ testProperty "large"     $ propSample large 0.7  -- sanity check for the benchmarks
      ]
  , localOption WallTime                                  -- benchmark using wall-time rather than CPU-time
  $ localOption (NumThreads 1)                            -- run each test sequentially with many cores
  $ localOption (mkTimeout 60_000_000)                    -- timeout each test after 60 s
  $ bgroup "bench"
      [                               bench "N1" $ nfAppIO (benchParallel large 0.7) 1
      , bcompareWithin 0.4 0.8 "N1" $ bench "N2" $ nfAppIO (benchParallel large 0.7) 2
      , bcompareWithin 0.2 0.6 "N1" $ bench "N4" $ nfAppIO (benchParallel large 0.7) 4
      , bcompareWithin 0.1 0.5 "N1" $ bench "N8" $ nfAppIO (benchParallel large 0.7) 8
      ]
  ]

propSample :: Graph -> Distance -> Property
propSample graph delta = property $ do
  let nodes = G.nodes graph
      order = G.order graph
  --
  src <- forAll $ Gen.element nodes
  dst <- forAll $ Gen.list (Range.linear 1 order) (Gen.element nodes)
  testSssp graph delta src dst

propArbitrary :: Gen Graph -> Distance -> Property
propArbitrary graph delta = property $ do
  g     <- forAll $ graph
  let order = G.order g
  src   <- forAll $ Gen.int (Range.constant 0 (order-1))
  dst   <- forAll $ Gen.list (Range.linear 1 order) (Gen.int (Range.constant 0 (order-1)))
  testSssp g delta src dst

testSssp :: Graph -> Distance -> Node -> [Node] -> PropertyT IO ()
testSssp graph delta src dst = do
  withFrozenCallStack $ ghciSuggestion graph delta src
  sp  <- evalIO $ deltaStepping False graph delta src
  let actual   = map (\d -> let x = sp V.! d in if isInfinite x then Nothing else Just x) dst
      expected = map (\d -> G.spLength src d graph) dst
  actual ~~~ expected

ghciSuggestion :: HasCallStack => Graph -> Distance -> Node -> PropertyT IO ()
ghciSuggestion graph delta src = do
  let graphStr = show graph
  when (length graphStr < 10000) $
    annotate
      $ "Run this test case in GHCi via:\n"
      ++ "  > cabal repl\n"
      ++ "  > import DeltaStepping\n"
      ++ "  > import Data.Graph.Inductive\n"
      ++ "  > deltaStepping True (" ++ graphStr ++ ") " ++ show delta ++ " " ++ show src

benchParallel :: Graph -> Distance -> Int -> IO (Vector Distance)
benchParallel graph delta n = do
  setNumCapabilities n
  deltaStepping False graph delta 0

large :: Graph
large =
  let g = Gen.arbitrary (Range.singleton 32768) (Range.singleton 131072) Gen.enumerated Gen.distance
   in case Gen.evalGen 99 (Seed.from 42) g of
        Nothing -> error "Could not generate sample graph"
        Just x  -> Tree.treeValue x

