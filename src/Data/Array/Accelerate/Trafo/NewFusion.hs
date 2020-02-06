{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeOperators         #-}
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
    letboundacc = letBindEverything acc
    graph = makeGraph letboundacc
    partition = orderPartition graph $ makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc

letBindEverything :: AST.Acc a -> LabelledAcc a
letBindEverything acc = evalState (letBindAcc acc) 1

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

letBindAcc :: AST.OpenAcc aenv a -> State Int (LabelledOpenAcc aenv a)
letBindAcc (AST.OpenAcc pacc) = LabelledOpenAcc <$> case pacc of
  AST.Alet lhs acc1 acc2 -> do
    acc1' <- letBindAcc acc1
    acc2' <- letBindAcc acc2
    return $ Alet lhs acc1' acc2' 

  AST.Avar (AST.ArrayVar idx) -> return $ Variable $ Avar $ ArrayVar idx
 
  AST.Apair acc1 acc2 -> letBind acc1 $ \w1 var1 ->
    letBind (w1 $:> acc2) $ \w2 var2 -> return $
      Variable $ Apair (w2 $:> var1) var2

  AST.Anil -> return $ Variable Anil

  AST.Apply f acc -> do
    n <- getInc
    f' <- letBindAfun f
    letBind acc $ \w var -> return $
      Apply n (w $:> f') var
 
  AST.Aforeign asm fun acc -> do
    n <- getInc
    fun' <- letBindAfun fun
    letBind acc $ \_ var -> return $ 
      Aforeign n asm fun' var

  AST.Acond e left right -> do
    n <- getInc
    e' <- letBindExp e
    left'  <- letBindAcc left
    right' <- letBindAcc right
    return $ Acond n e' left' right'

  AST.Awhile cond fun acc -> do
    n <- getInc
    cond' <- letBindAfun cond
    fun' <- letBindAfun fun
    letBind acc $ \w var -> return $ 
      Awhile n (w $:> cond') (w $:> fun') var

  AST.Use a -> do
    n <- getInc
    return $ Use n a

  AST.Unit e -> do
    n <- getInc
    e' <- letBindExp e
    return $ Unit n e'
 
  AST.Reshape sh acc -> do
    n <- getInc
    sh' <- letBindExp sh
    letBind acc (\w var -> return $ 
      Reshape n (w $:> sh') var)

  AST.Generate sh fun -> do
    n <- getInc
    sh' <- letBindExp sh
    fun' <- letBindFun fun
    return $ Generate n sh' fun'

-- TODO do these need to exist?
  AST.Transform{} -> undefined
  AST.Replicate{} -> undefined

  AST.Slice slidx acc e -> do
    n <- getInc
    e' <- letBindExp e
    letBind acc (\w var -> return $ 
      Slice n slidx var (w $:> e'))

  AST.Map f acc -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc $ \w var -> return $ 
      Map n (w $:> f') var

  AST.ZipWith f acc1 acc2 -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc1 $ \w1 var1 ->
      letBind (w1 $:> acc2) $ \w2 var2 -> return $ 
        ZipWith n (w2 . w1 $:> f') (w2 $:> var1) var2

  AST.Fold f e acc -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w var -> return $
      Fold n (w $:> f') (w $:> e') var

  AST.Fold1 f acc -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc $ \w var -> return $ 
      Fold1 n (w $:> f') var

  AST.FoldSeg f e acc seg -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w1 var1 -> 
      letBind (w1 $:> seg) $ \w2 var2 -> return $ 
        FoldSeg n (w2 . w1 $:> f') (w2 . w1 $:> e') (w2 $:> var1) var2

  AST.Fold1Seg f acc seg -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc $ \w1 var1 -> 
      letBind (w1 $:> seg) $ \w2 var2 ->
        return $ Fold1Seg n (w2 . w1 $:> f') (w2 $:> var1) var2

  AST.Scanl f e acc -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w var -> return $
      Scanl n (w $:> f') (w $:> e') var
    
  AST.Scanl' f e acc -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w var -> return $
      Scanl' n (w $:> f') (w $:> e') var

  AST.Scanl1 f acc -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc $ \w var -> return $
      Scanl1 n (w $:> f') var

  AST.Scanr f e acc -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w var -> return $
      Scanr n (w $:> f') (w $:> e') var
    
  AST.Scanr' f e acc -> do
    n <- getInc
    f' <- letBindFun f
    e' <- letBindExp e
    letBind acc $ \w var -> return $
      Scanr' n (w $:> f') (w $:> e') var

  AST.Scanr1 f acc -> do
    n <- getInc
    f' <- letBindFun f
    letBind acc $ \w var -> return $
      Scanr1 n (w $:> f') var

  AST.Permute f acc1 g acc2 -> do
    n <- getInc
    f' <- letBindFun f
    g' <- letBindFun g
    letBind acc1 $ \w1 var1 -> letBind (w1 $:> acc2) $ \w2 var2 -> return $
      Permute n (w2 . w1 $:> f') (w2 $:> var1) (w2 . w1 $:> g') var2

  AST.Backpermute e f acc -> do
    n <- getInc
    e' <- letBindExp e
    f' <- letBindFun f
    letBind acc $ \w var -> return $
      Backpermute n (w $:> e') (w $:> f') var

  AST.Stencil f b acc -> do
    n <- getInc
    f' <- letBindFun f
    b' <- letBindBoundary b
    letBind acc $ \w var -> return $
      Stencil n (w $:> f') (w $:> b') var

  AST.Stencil2 f b1 acc1 b2 acc2 -> do
    n <- getInc
    f' <- letBindFun f
    b1' <- letBindBoundary b1
    b2' <- letBindBoundary b2
    letBind acc1 $ \w1 var1 -> letBind (w1 $:> acc2) $ \w2 var2 -> return $
      Stencil2 n (w2 . w1 $:> f') (w2 . w1 $:> b1') (w2 $:> var1) (w2 . w1 $:> b2') var2


letBindAfun :: PreOpenAfun OpenAcc aenv a -> State Int (PreOpenAfun LabelledOpenAcc aenv a)
letBindAfun (Abody acc) = Abody <$> letBindAcc acc
letBindAfun (Alam lhs body) = Alam lhs <$> letBindAfun body


-- abstracts a very common pattern in 'letBindEverything
letBind :: AST.OpenAcc env a -> (forall env'. env :> env' -> BoundVariable env' a -> State Int (PreLabelledAcc LabelledOpenAcc env' b)) -> State Int (PreLabelledAcc LabelledOpenAcc env b)
letBind acc cont = do
  acc' <- letBindAcc acc
  case makeLHSBV acc' of
    Exists (LHSBV lhs var) ->
      Alet lhs acc' . LabelledOpenAcc <$> cont (weakenWithLHS lhs) var
{-
letBindFun :: PreOpenAfun AST.OpenAcc env a -> (forall env'. LeftHandSide a env env' -> BoundVariable env' a -> State Int (PreLabelledAcc LabelledOpenAcc env' b)) -> State Int (PreLabelledAcc LabelledOpenAcc env b)
letBindFun acc cont = do
  acc' <- letBindAfun acc
  case makeLHSBV acc' of
    Exists (LHSBV lhs var) ->
      Alet lhs acc' . LabelledOpenAcc <$> cont lhs var
-}

makeLHSBV :: HasArraysRepr f => f aenv a -> Exists (LHSBoundVar a env)
makeLHSBV = makeLHSBV' . arraysRepr

makeLHSBV' :: ArraysR a -> Exists (LHSBoundVar a env)
makeLHSBV' a = case a of
  ArraysRunit -> Exists $ LHSBV (LeftHandSideWildcard ArraysRunit) Anil
  ArraysRarray -> Exists $ LHSBV LeftHandSideArray (Avar $ ArrayVar ZeroIdx)
  ArraysRpair left right -> case makeLHSBV' left of 
    Exists  (LHSBV leftlhs  leftvar) -> case makeLHSBV' right of
      Exists (LHSBV rightlhs rightvar) ->
        Exists $ LHSBV (LeftHandSidePair leftlhs rightlhs) (Apair (weakenWithLHS rightlhs `weaken` leftvar) rightvar)

data LHSBoundVar a env env' = LHSBV (LeftHandSide a env env') (BoundVariable env' a)


getInc :: State Int NodeId
getInc = modify (+1) >> gets NodeId


letBindExp :: OpenExp env aenv t -> State Int (LabelledOpenExp env aenv t)
letBindExp openexp =
  case openexp of
    Let bnd body            -> do
      bnd'  <- letBindExp bnd
      body' <- letBindExp body
      return $ Let bnd' body'
    Var ix                  -> return $ Var ix
    Const c                 -> return $ Const c
    Undef                   -> return Undef
    Tuple tup               -> Tuple <$> letBindTup tup
    Prj ix t                -> Prj ix <$> letBindExp t
    IndexNil                -> return IndexNil
    IndexCons sh sz         -> do
      sh' <- letBindExp sh
      sz' <- letBindExp sz
      return $ IndexCons sh' sz'
    IndexHead sh            -> IndexHead <$> letBindExp sh
    IndexTail sh            -> IndexTail <$> letBindExp sh
    IndexAny                -> return IndexAny
    IndexSlice x ix sh      -> do
      ix' <- letBindExp ix
      sh' <- letBindExp sh
      return $ IndexSlice x ix' sh'
    IndexFull x ix sl       -> do
      ix' <- letBindExp ix
      sl' <- letBindExp sl
      return $ IndexFull x ix' sl'
    ToIndex sh ix           -> do
      sh' <- letBindExp sh
      ix' <- letBindExp ix
      return $ ToIndex sh' ix'
    FromIndex sh ix         -> do
      sh' <- letBindExp sh
      ix' <- letBindExp ix
      return $ FromIndex sh' ix'
    Cond p t e              -> do
      p' <- letBindExp p
      t' <- letBindExp t
      e' <- letBindExp e      
      return $ Cond p' t' e'
    While p f x             -> do
      p' <- letBindFun p
      f' <- letBindFun f
      x' <- letBindExp x      
      return $ While p' f' x'
    PrimConst c             -> return $ PrimConst c
    PrimApp f x             -> PrimApp f <$> letBindExp x
    Index a sh              -> do
      a' <- letBindAcc a
      sh' <- letBindExp sh
      return $ Index a' sh'
    LinearIndex a i         -> do
      a' <- letBindAcc a
      i' <- letBindExp i
      return $ LinearIndex a' i'
    Shape a                 -> Shape <$> letBindAcc a
    ShapeSize sh            -> ShapeSize <$> letBindExp sh
    Intersect s t           -> do
      s' <- letBindExp s
      t' <- letBindExp t
      return $ Intersect s' t'
    Union s t               -> do
      s' <- letBindExp s
      t' <- letBindExp t
      return $ Union s' t'
    Foreign ff f e          -> do
      f' <- letBindFun f
      e' <- letBindExp e
      return $ Foreign ff f' e'
    Coerce e                -> Coerce <$> letBindExp e
  where
    letBindTup :: Tuple (OpenExp env aenv) t -> State Int (Tuple (LabelledOpenExp env aenv) t)
    letBindTup NilTup        = return NilTup
    letBindTup (SnocTup t e) = do
      e' <- letBindExp e
      t' <- letBindTup t 
      return $ SnocTup t' e'


letBindFun :: OpenFun env aenv f -> State Int (LabelledOpenFun env aenv f)
letBindFun (Lam f)  = Lam <$> letBindFun f
letBindFun (Body b) = Body <$> letBindExp b


letBindBoundary :: PreBoundary OpenAcc env a -> State Int (PreBoundary LabelledOpenAcc env a)
letBindBoundary Clamp        = return Clamp
letBindBoundary Mirror       = return Mirror
letBindBoundary Wrap         = return Wrap
letBindBoundary (Constant c) = return $ Constant c
letBindBoundary (Function f) = Function <$> letBindFun f











infix 8 $:>
($:>) :: Sink f => env :> env' -> f env t -> f env' t
($:>) = weaken


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

