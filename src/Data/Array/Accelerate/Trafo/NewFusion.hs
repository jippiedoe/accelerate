module Data.Array.Accelerate.Trafo.NewFusion (doFusion, dotesting) where


import Data.Array.Accelerate.Trafo.NewFusion.AST
import Control.Monad.State
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.NewFusion.LetBind
import Data.Array.Accelerate.Trafo.NewFusion.Solver
import qualified Data.IntMap.Strict as IM
import System.IO.Unsafe

doFusion :: Acc a -> FusedAcc a
doFusion acc = fusedacc
  where
    letboundacc = letBindEverything acc
    graph = makeFullGraph letboundacc
    partition = makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc

dotesting :: OpenAcc env a -> IO (OpenAcc env a)
dotesting acc = do print "newfusion start"
                   let lbacc = letBindEverything acc
                   let graph = makeFullGraph lbacc
                   print "graph:"
                   print graph
                   let lp    = makeILP graph
                   --callGLPKTest lp
                   solu <- callGLPK lp
                   print $ groupNodes solu
                   return acc

letBindEverything :: OpenAcc env a -> LabelledOpenAcc env a
letBindEverything acc = evalState (letBindAcc acc) 1

makeFullGraph :: LabelledOpenAcc env a -> DirectedAcyclicGraph
makeFullGraph acc = snd $ makeGraph acc [] $ DAG IM.empty []

makePartition :: DirectedAcyclicGraph -> [[NodeId]]
makePartition = groupNodes . unsafePerformIO . callGLPK . makeILP

rewriteAST :: LabelledOpenAcc aenv a -> [[NodeId]] -> GroupedLabelledAcc aenv a
rewriteAST = undefined

finalizeFusion :: GroupedLabelledAcc () a -> FusedAcc a
finalizeFusion = undefined