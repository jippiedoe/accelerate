{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}



module Data.Array.Accelerate.Trafo.NewFusion {- (export list) -} where

import Data.Array.Accelerate.Trafo.NewFusionASTs
import Control.Monad.State
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST        hiding (PreOpenAcc(..))
import qualified Data.Array.Accelerate.AST    as AST


doFusion :: AST.Acc a -> FusedAcc a
doFusion acc = fusedacc
  where
    letboundacc = letBindEverything acc
    graph = makeGraph letboundacc
    partition = orderPartition graph $ makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc

letBindEverything :: AST.Acc a -> LabelledAcc a
letBindEverything acc = evalState (letBindEverythingWith acc) 1

makeGraph :: LabelledAcc a -> DirectedAcyclicGraph
makeGraph = undefined

-- makes the ILP and calls the solver.
makePartition :: DirectedAcyclicGraph -> [[NodeId]]
makePartition = undefined

orderPartition :: DirectedAcyclicGraph -> [[NodeId]] -> [[NodeId]]
orderPartition = undefined

rewriteAST :: LabelledOpenAcc aenv a -> [[NodeId]] -> GroupedLabelledAcc aenv a
rewriteAST = undefined

finalizeFusion :: GroupedLabelledAcc () a -> FusedAcc a
finalizeFusion = undefined

data DirectedAcyclicGraph = DAG 
  { nodes :: [NodeId]
  , dependencies :: [(NodeId, NodeId, Int)] -- the nodes with these id's must obey this partial order in the fusion, and fusing them will give the associated profit
  , fusionPreventingEdges :: [(NodeId, NodeId)] -- these nodes can't be in the same partition
  }

letBindEverythingWith :: AST.OpenAcc aenv a -> State Int (LabelledOpenAcc aenv a)
letBindEverythingWith (AST.OpenAcc pacc) = LabelledOpenAcc <$> case pacc of
  AST.Alet lhs acc1 acc2 -> do
    acc1' <- letBindEverythingWith acc1
    acc2' <- letBindEverythingWith acc2
    return $ Alet lhs acc1' acc2'

  AST.Avar (AST.ArrayVar idx) -> return $ Avar idx
 
  {-AST.Apair acc1 acc2 -> do -- Openacc env (as,bs)
    acc1' <- letBindEverythingWith acc1 -- LabelledOpenAcc env as
    acc2' <- letBindEverythingWith acc2 -- LabelledOpenAcc env bs
    return $ Alet (makelhs acc1') acc1' $ 
      LabelledOpenAcc $ 
        Alet (makelhs acc2') acc2' $ 
          LabelledOpenAcc $ 
            Apair (SuccIdx ZeroIdx) ZeroIdx
-}
makelhs :: ArraysR a -> LeftHandSide a env (env, a)
makelhs arrra = case arrra of
  ArraysRunit -> LeftHandSideWildcard ArraysRunit
  ArraysRarray -> LeftHandSideArray
  ArraysRpair left right -> LeftHandSidePair (makelhs left) (makelhs right)

{-
ALet: special case
AVar, APair, ANil, Apply, AForeign, ACond, AWhile, Use, Unit, Reshape, replicate, slice: ?
producers: Generate, transform, map, zipwith (in one or two inputs?): in all directions, with almost anything
backpermute is a producer, but only if the input is the target shape. It can't vertically happen after non-producers, but can vertically happen before anything.
Permute is the opposite: fuses vertically after anything, but not before.
fold(1)(Seg): in all directions with producers and with other folds
scan(l/r)(1)('): in all directions with producers and with other scans
permute: in all directions with producers and with other permutes
stencil(2): in all directions with producers and with other stencils
-}

