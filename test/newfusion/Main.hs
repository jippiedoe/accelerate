module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I

main :: IO ()
main = do
  print "starting test/newfusion! woo!"
  print $ I.run normalise2


-- from "Fusing Filters with Integer Linear Programming", but replacing the filter with a prefixsum
normalise2 :: A.Acc (A.Array A.DIM1 Int, A.Array A.DIM1 Int)
normalise2 = A.T2 ys1 ys2 where
  xs, gts, ys1, ys2 :: A.Acc (A.Array A.DIM1 Int)
  sum1, sum2 :: A.Acc (A.Array A.DIM0 Int)
  xs = A.use $ A.fromList (A.Z A.:. 3) [4,5,6]
  sum1 = A.fold (+) 0 xs
  gts = A.scanl (+) 0 xs
  sum2 = A.fold (+) 0 gts
  ys1 = A.map (`A.div` (sum1 A.! A.constant A.Z)) xs
  ys2 = A.map (`A.div` (sum2 A.! A.constant A.Z)) xs