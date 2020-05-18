module Main where
import Data.Array.Accelerate.Trafo.NewFusion.NewInterpreter

main :: IO ()
main = test

-- import qualified Data.Array.Accelerate as A
-- import qualified Data.Array.Accelerate.Interpreter as I

-- main :: IO ()
-- main = do
--   print "starting test/newfusion! woo!"
--   print $ I.run normalise2'


-- testwhile :: A.Acc (A.Array A.DIM1 Int)
-- testwhile = A.awhile (const $ A.use $ A.fromList A.Z [True]) (A.map (+1)) (A.use $ A.fromList (A.Z A.:. 1) [1])


-- -- from "Fusing Filters with Integer Linear Programming", but replacing the filter with a prefixsum
-- normalise2 :: A.Acc (A.Array A.DIM1 Int, A.Array A.DIM1 Int)
-- normalise2 = A.T2 ys1 ys2 where                       -- 7, 12   [1]
--   xs, scn, ys1, ys2 :: A.Acc (A.Array A.DIM1 Int)
--   sum1, sum2 :: A.Acc (A.Array A.DIM0 Int)
--   xs = A.use $ A.fromList (A.Z A.:. 30) [4..]         -- 2       [0]
--   sum1 = A.fold (+) 0 xs                              -- 4       [0]
--   scn = A.scanl (+) 0 xs                              -- 8       [0]
--   sum2 = A.fold (+) 0 scn                             -- 9       [0]
--   ys1 = A.map (`A.div` (sum1 A.! A.constant A.Z)) xs  -- 5  (7)  [1]
--   ys2 = A.map (`A.div` (sum2 A.! A.constant A.Z)) xs  -- 10 (12) [1]




-- -- like above, but with a zipWith at the top level to fuse ys1 and ys2
-- normalise2' :: A.Acc (A.Array A.DIM1 Int)
-- normalise2' = A.zipWith (*) ys1 ys2 where
--   xs, scn, ys1, ys2 :: A.Acc (A.Array A.DIM1 Int)
--   sum1, sum2 :: A.Acc (A.Array A.DIM0 Int)
--   xs = A.use $ A.fromList (A.Z A.:. 30) [4..]
--   sum1 = A.fold (+) 0 xs
--   scn = A.scanl (+) 0 xs
--   sum2 = A.fold (+) 0 scn
--   ys1 = A.map (`A.div` (sum1 A.! A.constant A.Z)) xs
--   ys2 = A.map (`A.div` (sum2 A.! A.constant A.Z)) xs


-- {-
-- xs == For (30) {OneToOne}

-- sum1 == For (30) {ManyToOne}

-- sum2 | scn == For (30) {Before {OneToOne} {ManyToOne}}

-- sum1 - (sum2 | scn) == For (30) {Besides {ManyToOne} {Before {OneToOne} {ManyToOne}}}

-- xs \ (sum1 - (sum2 | scn)) == For (30) {Before' {xs} {Besides {sum1} {Before {scn} {sum2}}}}
-- -}