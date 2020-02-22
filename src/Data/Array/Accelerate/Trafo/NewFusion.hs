module Data.Array.Accelerate.Trafo.NewFusion (doFusion) where


import Data.Array.Accelerate.Trafo.NewFusion.AST
import Control.Monad.State
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.NewFusion.LetBind
import Data.Array.Accelerate.Trafo.NewFusion.Solver

doFusion :: Acc a -> FusedAcc a
doFusion acc = fusedacc
  where
    letboundacc = letBindEverything acc
    graph = makeFullGraph letboundacc
    partition = orderPartition graph $ makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc


letBindEverything :: Acc a -> LabelledAcc a
letBindEverything acc = evalState (letBindAcc acc) 1

makeFullGraph :: LabelledAcc a -> DirectedAcyclicGraph
makeFullGraph acc = snd $ makeGraph acc [] undefined

-- makes the ILP and calls the solver.
makePartition :: DirectedAcyclicGraph -> [[NodeId]]
makePartition = undefined

orderPartition :: DirectedAcyclicGraph -> [[NodeId]] -> [[NodeId]]
orderPartition = undefined

rewriteAST :: LabelledOpenAcc aenv a -> [[NodeId]] -> GroupedLabelledAcc aenv a
rewriteAST = undefined

finalizeFusion :: GroupedLabelledAcc () a -> FusedAcc a
finalizeFusion = undefined
