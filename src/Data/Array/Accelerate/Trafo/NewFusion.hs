{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE RankNTypes            #-}


module Data.Array.Accelerate.Trafo.NewFusion {- (export list) -} where

import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.NewFusionASTs
import Control.Monad.State
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST        hiding (PreOpenAcc(..))
import qualified Data.Array.Accelerate.AST    as AST


doFusion :: AST.Acc a -> FusedAcc a
doFusion acc = fusedacc
  where
    letboundacc = letBindEverything' acc
    graph = makeGraph letboundacc
    partition = orderPartition graph $ makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc

letBindEverything' :: AST.Acc a -> LabelledAcc a
letBindEverything' acc = evalState (letBindEverything acc) 1

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

letBindEverything :: AST.OpenAcc aenv a -> State Int (LabelledOpenAcc aenv a)
letBindEverything (AST.OpenAcc pacc) = LabelledOpenAcc <$> case pacc of
  AST.Alet lhs acc1 acc2 -> do
    acc1' <- letBindEverything acc1
    acc2' <- letBindEverything acc2
    return $ Alet lhs acc1' acc2' 

  AST.Avar (AST.ArrayVar idx) -> return $ Variable $ Avar $ ArrayVar idx
 
  AST.Apair acc1 acc2 -> do
    acc1' <- letBindEverything acc1
    acc2' <- letBindEverything acc2
    case makeLHSBV acc1' of
     Exists (LHSBV lhs1 var1 :: LHSBoundVar b aenv aenv') ->
      case makeLHSBV acc2' of
       Exists (LHSBV lhs2 var2 :: LHSBoundVar c aenv' aenv'') ->
        return $ Alet lhs1 acc1' $ LabelledOpenAcc $ Alet lhs2 (weakenWithLHS lhs1 `weaken` acc2') $ LabelledOpenAcc $ Variable $ Apair (weakenWithLHS lhs2 `weaken` var1) var2

  AST.Anil -> return $ Variable Anil

  --TODO Apply
 
  AST.Aforeign asm fun acc -> do
    n <- getInc
    letBind acc (\lhs var -> Aforeign n asm fun var)

  AST.Acond e left right -> do
    n <- getInc
    left'  <- letBindEverything left
    right' <- letBindEverything right
    return $ Acond n e left' right'

  AST.Awhile cond fun acc -> do
    n <- getInc
    letBind acc (\lhs var ->
      Awhile n 
      (weakenWithLHS lhs `weaken` cond)
      (weakenWithLHS lhs `weaken` fun)
      var)

  AST.Use a -> do
    n <- getInc
    return $ Use n a

  AST.Unit e -> do
    n <- getInc
    return $ Unit n e
 
  AST.Reshape sh acc -> do
    n <- getInc
    letBind acc (\lhs var -> Reshape n (weakenWithLHS lhs `weaken` sh) var)

  AST.Generate sh fun -> do
    n <- getInc
    return $ Generate n sh fun

-- TODO transform
-- TODO Replicate

  AST.Slice slidx acc e -> do
    n <- getInc
    letBind acc (\lhs var -> Slice n slidx var (weakenWithLHS lhs `weaken` e))

  AST.Map f acc -> do
    n <- getInc
    letBind acc $ \lhs var -> Map n (weakenWithLHS lhs `weaken` f) var

  AST.ZipWith f acc1 acc2 -> do
    n <- getInc
    acc1' <- letBindEverything acc1
    case makeLHSBV acc1' of
      Exists (LHSBV lhs1 var1) ->
        Alet lhs1 acc1' . LabelledOpenAcc <$> letBind (weakenWithLHS lhs1 `weaken` acc2)
          (\lhs2 var2 -> ZipWith n (weakenWithLHS (LeftHandSidePair lhs1 lhs2) `weaken` f) (weakenWithLHS lhs2 `weaken` var1) var2)

  AST.Fold f e acc -> do
    n <- getInc
    letBind acc $ \lhs var -> Fold n (weakenWithLHS lhs `weaken` f) (weakenWithLHS lhs `weaken` e) var

  -- 13 more

-- abstracts a very common pattern in 'letBindEverything'
letBind :: AST.OpenAcc env a -> (forall env'. LeftHandSide a env env' -> BoundVariable env' a -> PreLabelledAcc LabelledOpenAcc env' b) -> State Int (PreLabelledAcc LabelledOpenAcc env b)
letBind acc cont = do
  acc' <- letBindEverything acc
  case makeLHSBV acc' of
    Exists (LHSBV lhs var) ->
      return $ Alet lhs acc' $ LabelledOpenAcc $ cont lhs var



makeLHSBV :: HasArraysRepr f => f aenv a -> Exists (LHSBoundVar a env)
makeLHSBV = makeLHSBV' . arraysRepr

makeLHSBV' :: ArraysR a -> Exists (LHSBoundVar a env)
makeLHSBV' a = case a of
  ArraysRunit -> Exists $ LHSBV (LeftHandSideWildcard ArraysRunit) Anil
  ArraysRarray -> Exists $ LHSBV LeftHandSideArray (Avar $ ArrayVar ZeroIdx)
  ArraysRpair left right -> case makeLHSBV' left of 
   Exists  (LHSBV leftlhs  leftvar  :: LHSBoundVar b env  env' ) -> case makeLHSBV' right of
    Exists (LHSBV rightlhs rightvar :: LHSBoundVar c env' env'') ->
      Exists $ LHSBV (LeftHandSidePair leftlhs rightlhs) (Apair (weakenWithLHS rightlhs `weaken` leftvar) rightvar)

data LHSBoundVar a env env' = LHSBV (LeftHandSide a env env') (BoundVariable env' a)


getInc :: State Int NodeId
getInc = modify (+1) >> gets NodeId

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

