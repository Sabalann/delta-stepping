{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE TupleSections #-}

module Test.Gen where

import Data.Graph.Inductive                                         ( Gr, Node, Edge, UNode, LNode, LEdge, mkGraph )
import Hedgehog                                                     ( Gen, Range )
import qualified Data.Set                                           as Set
import qualified Hedgehog.Gen                                       as Gen
import qualified Hedgehog.Range                                     as Range


_MAX_NODES :: Int
_MAX_NODES = 128

_MAX_EDGES :: Int
_MAX_EDGES = 3 * _MAX_NODES

_MIN_DIST, _MAX_DIST :: Float
_MIN_DIST = 0
_MAX_DIST = 1

node :: Int -> Gen Node
node o = Gen.int (Range.constant 0 (o-1))

edge :: Gen Node -> Gen Edge
edge n = (,) <$> n <*> n

unlabelled :: Node -> Gen UNode
unlabelled x = return (x, ())

enumerated :: Node -> Gen (LNode String)
enumerated x = return (x, show x)

distance :: Edge -> Gen (LEdge Float)
distance (n,m) = (n,m,) <$> Gen.float (Range.constant _MIN_DIST _MAX_DIST)


-- Generate a graph with all nodes in a single line (with forward and backward
-- edges)
--
line :: Range Int
     -> (Node -> Gen (LNode a))        -- generate a label for a given node
     -> (Edge -> Gen (LEdge b))        -- generate a weight for a given edge
     -> Gen (Gr a b)
line r_order g_label g_weight = do
  order  <- Gen.int r_order
  lnodes <- mapM g_label [0 .. order-1]
  ledges <- let go !i | i >= order-1 = return []
                      | otherwise    = do
                          x <- g_weight (i, i+1)
                          y <- g_weight (i+1, i)
                          w <- go (i+1)
                          return (x : y : w)
             in go 0
  return $! mkGraph lnodes ledges

-- Generate a graph with all nodes in a (one-way) loop
--
loop :: Range Int
     -> (Node -> Gen (LNode a))        -- generate a label for a given node
     -> (Edge -> Gen (LEdge b))        -- generate a weight for a given edge
     -> Gen (Gr a b)
loop r_order g_label g_weight = do
  order  <- Gen.int r_order
  lnodes <- mapM g_label [0 .. order-1]
  ledges <- let go !i | i >= order - 1 = do
                          x <- g_weight (i, 0)
                          return [x]
                      | otherwise = do
                          x <- g_weight (i, i+1)
                          y <- go (i+1)
                          return (x : y)
             in go 0
  return $! mkGraph lnodes ledges

-- Generate an arbitrary graph with no multiple edges (loops allowed)
--
arbitrary
    :: Range Int                      -- number of nodes to generate
    -> Range Int                      -- number of edges to generate
    -> (Node -> Gen (LNode a))        -- generate a label for a given node
    -> (Edge -> Gen (LEdge b))        -- generate a weight for a given edge
    -> Gen (Gr a b)
arbitrary r_order r_edges g_label g_weight = do
  order  <- Gen.int r_order
  edges  <- Gen.set r_edges (edge (node order))
  lnodes <- mapM g_label [0 .. (order-1)]
  ledges <- mapM g_weight (Set.elems edges)
  --
  return $! mkGraph lnodes ledges

