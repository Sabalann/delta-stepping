
module Sample where

import Data.Graph.Inductive
import Data.Graph.Inductive.Dot

import System.Directory
import System.FilePath
import System.IO
import System.Process
import Text.Printf


-- Convert the given graph to a .png file and save it into the temporary
-- directory. The path to the file is printed.
--
-- This requires the command "dot" to be available in the path. This is
-- available as part of graphviz package:
--
-- > https://graphviz.org/download/
--
graphToDot :: Gr String Float -> IO ()
graphToDot g = do
  tmp      <- canonicalizePath =<< getTemporaryDirectory
  (dot, h) <- openTempFile tmp "graph.dot"
  let png = dot -<.> "png"
  hPutStr h (showDot (fglToDot g))
  hClose h
  callProcess "dot" ["-Tpng", "-o", png, dot]
  printf "graph written to file: %s\n" png


-- https://en.wikipedia.org/wiki/Parallel_single-source_shortest_path_algorithm#Delta_stepping_algorithm
--
sample1 :: Gr String Float
sample1 =
  mkGraph
    (zip [0..] (map return "ABCDEFG"))
    [ (0,1,3), (0,3,5), (0,4,3), (0,6,3)  -- A
    , (1,0,3), (1,2,3)                    -- B
    , (2,1,3), (2,3,1)                    -- C
    , (3,2,1), (3,0,5)                    -- D
    , (4,0,3), (4,5,5)                    -- E
    , (5,4,5)                             -- F
    , (6,0,3)                             -- G
    ]

-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--
-- [(0,"A")
-- ,(1,"B")
-- ,(2,"C")
-- ,(3,"D")
-- ,(4,"E")
-- ,(5,"F")
-- ,(6,"G")
-- ,(7,"H")
-- ,(8,"I")
-- ,(9,"J")
-- ,(10,"K")
-- ,(11,"L")
-- ,(12,"M")
-- ,(13,"N")
-- ,(14,"O")
-- ,(15,"P")
-- ,(16,"Q")
-- ,(17,"R")
-- ,(18,"S")
-- ,(19,"T")
-- ,(20,"U")
-- ,(21,"V")
-- ,(22,"W")
-- ,(23,"X")
-- ,(24,"Y")
-- ,(25,"Z")
-- ,(26,"AA")
-- ,(27,"AB")
-- ,(28,"AC")
-- ,(29,"AD")
-- ,(30,"AE")
-- ,(31,"AF")
-- ,(32,"AG")
-- ,(33,"AH")
-- ,(34,"AI")
-- ,(35,"AJ")
-- ,(36,"AK")]
--
sample2 :: Gr String Float
sample2 =
  let labels = [] : [ xs ++ [x] | xs <- labels, x <- ['A' .. 'Z'] ]
   in undir
    $ mkGraph
        (zip [0..36] (tail labels))
        [ (0,1,3), (0,2,3), (0,3,5), (0,4,3)          -- A .. B, C, D, E
        , (1,5,3), (1,6,2), (1,7,3)                   -- B .. F, G, H
        , (2,8,2), (2,9,5), (2,10,4)                  -- C .. I, J, K
        , (3,5,1), (3,12,1), (3,13,1), (3,11,2)       -- D .. F, M, N, L
        , (4,16,3), (4,15,2), (4,17,3), (4,14,2)      -- E .. Q, P, R, O
        , (6,34,5), (6,32,2), (6,19,1), (6,33,1)      -- G .. AI, AG, T, AH
        , (7,27,1), (7,28,3)                          -- H .. AB, AC
        , (8,35,4), (8,36,4)                          -- I .. AJ, AK
        , (10,21,3), (10,18,3), (10,23,2), (10,20,1)  -- K .. V, S, X, U
        , (11,31,1)                                   -- L .. AF
        , (13,30,2), (13,29,3), (13,31,1)             -- N .. AE, AD, AF
        , (14,26,1)                                   -- O .. AA
        , (16,20,6), (16,25,4)                        -- Q .. U, Z
        , (20,24,2), (20,22,3)                        -- U .. Y, W
        , (33,28,1)                                   -- AH .. AC
        ]

