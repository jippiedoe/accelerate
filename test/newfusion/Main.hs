module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I

main :: IO ()
main = do
  print "starting test/newfusion! woo!"
  print $ I.run normalise2'


-- from "Fusing Filters with Integer Linear Programming", but replacing the filter with a prefixsum
normalise2 :: A.Acc (A.Array A.DIM1 Int, A.Array A.DIM1 Int)
normalise2 = A.T2 ys1 ys2 where                       -- (9, 16)
  xs, gts, ys1, ys2 :: A.Acc (A.Array A.DIM1 Int)
  sum1, sum2 :: A.Acc (A.Array A.DIM0 Int)
  xs = A.use $ A.fromList (A.Z A.:. 3) [4,5,6]        -- 2 (4, 6, 10, 13) [0]
  sum1 = A.fold (+) 0 xs                              -- (4) 5 [0]
  gts = A.scanl (+) 0 xs                              -- (10) 11 [0]
  sum2 = A.fold (+) 0 gts                             -- 12 [0] {note: 11 doesn't get shared so no extra variable for once!}
  ys1 = A.map (`A.div` (sum1 A.! A.constant A.Z)) xs  -- (6) 7 (9) [1]
  ys2 = A.map (`A.div` (sum2 A.! A.constant A.Z)) xs  -- (13) 14 (16) [12]

-- like above, but with a zipWith at the top level to fuse ys1 and ys2
normalise2' :: A.Acc (A.Array A.DIM1 Int)
normalise2' = A.zipWith (*) ys1 ys2 where                       -- (6, 12) 14 [1]
  xs, gts, ys1, ys2 :: A.Acc (A.Array A.DIM1 Int)
  sum1, sum2 :: A.Acc (A.Array A.DIM0 Int)
  xs = A.use $ A.fromList (A.Z A.:. 3) [4,5,6]        -- 2 (3, 5, 8, 11) [0]
  sum1 = A.fold (+) 0 xs                              -- (3) 4 [0]
  gts = A.scanl (+) 0 xs                              -- (8) 9 [0]
  sum2 = A.fold (+) 0 gts                             -- (9) 10 [0] {note: 11 doesn't get shared so no extra variable for once!}
  ys1 = A.map (`A.div` (sum1 A.! A.constant A.Z)) xs  -- (5) 6 [1]
  ys2 = A.map (`A.div` (sum2 A.! A.constant A.Z)) xs  -- (11) 12 [1]