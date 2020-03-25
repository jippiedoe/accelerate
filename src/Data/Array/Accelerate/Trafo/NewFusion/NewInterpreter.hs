{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}

module Data.Array.Accelerate.Trafo.NewFusion.NewInterpreter
  ( Smart.Acc
  , Arrays
  , AST.Afunction
  , AST.AfunctionR
  ,
  -- * Interpret an array expression
  --run, run1, runN,

  -- Internal (hidden)
  --   evalPrj
  -- , evalPrim
  -- , evalPrimConst
  -- , evalUndef
  -- , evalCoerce
  --, testThis
  )
where

-- standard libraries
import           Control.Monad
import           Control.Monad.ST
import           Data.Bits
import           Data.Char                      ( chr
                                                , ord
                                                )
import           Data.Primitive.ByteArray
import           Data.Primitive.Types
import           Data.Typeable
import           System.IO.Unsafe               ( unsafePerformIO )
import           Text.Printf                    ( printf )
import           Unsafe.Coerce
import           Prelude                 hiding ( (!!)
                                                , sum
                                                )
-- friends
import           Data.Array.Accelerate.Trafo.NewFusion.AST
                                         hiding ( PreLabelledAcc(..) )

import           Data.Array.Accelerate.AST
                                         hiding ( Boundary
                                                , PreBoundary(..)
                                                , PreOpenAcc(..)
                                                )
import           Data.Array.Accelerate.Analysis.Type
                                                ( sizeOfScalarType
                                                , sizeOfSingleType
                                                )
import           Data.Array.Accelerate.Array.Data
import           Data.Array.Accelerate.Array.Representation
                                                ( SliceIndex(..) )
import           Data.Array.Accelerate.Array.Sugar
import           Data.Array.Accelerate.Error
import           Data.Array.Accelerate.Product
import           Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST     as AST
import qualified Data.Array.Accelerate.Smart   as Smart
import qualified Data.Array.Accelerate.Trafo   as AST


import           Control.Monad.State.Strict
import           Data.Foldable
import           Data.Maybe
import           Data.Array.Accelerate.Analysis.Match




data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e) => ValArr env -> Array sh e -> ValArr (env, Array sh e)





data HorizontalFusion left right res where
  Done :: HorizontalFusion () () ()
  Righty :: HorizontalFusion () b b -> HorizontalFusion () (b, Array sh e) (b, Array sh e)
  Lefty  :: HorizontalFusion a  b c -> HorizontalFusion (a, Array sh e)  b (c, Array sh e)


data IdxSpaceTransform phantom real where
  Id :: IdxSpaceTransform a a
  Fn :: (Int -> Int)
     -> IdxSpaceTransform phantom real
     -> IdxSpaceTransform (phantom, Array sh e) (real, Array sh' e)

compose :: IdxSpaceTransform a b -> IdxSpaceTransform b c -> IdxSpaceTransform a c
compose = undefined


--IR
data IntermediateRep permanentIn tempIn out where
  Void :: IntermediateRep () () ()
  -- Id   ::(Elt e, Shape sh)
  --      => IntermediateRep a b
  --      -> IntermediateRep (a, Array sh e) (b, Array sh e)
  For  :: IntermediateRep pin tin out
       -> Int -- the number of times to loop
       -> IdxSpaceTransform tin tin'
       -> IdxSpaceTransform out out'
       -> IntermediateRep pin tin' out' -- TODO does pin also change dimensions here?
  -- vertical
  Before  :: LoopBody        pin a b
          -> IntermediateRep pin b c
          -> IntermediateRep pin a c
  After   :: IntermediateRep pin a b
          -> LoopBody        pin b c
          -> IntermediateRep pin a c
  -- diagonal
  Before' :: HorizontalFusion b c hor
          -> LoopBody        pin a b
          -> IntermediateRep pin b c
          -> IntermediateRep pin a hor
  After'  :: HorizontalFusion b c hor
          -> IntermediateRep pin a b
          -> LoopBody        pin b c
          -> IntermediateRep pin a hor
  -- horizontal
  Besides :: HorizontalFusion b c hor
          -> LoopBody        pin a b
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor

data LoopBodyWrapper a b c where
  LBW :: LoopBody a b c
      -> (forall b'. IdxSpaceTransform b b' -> Exists (IdxSpaceTransform c))
      -> LoopBodyWrapper a b c

data LoopBody permIn tempIn out where
  Base :: LoopBody  pin a a
  Take :: LoopBody' pin a b
       -> LoopBody  pin c d
       -> LoopBody  pin (c, a) (d, b)
  Drop :: LoopBody  pin a b
       -> LoopBody  pin (a,x) (b,x)

data LoopBody' permIn tempIn out where
  OneToOne ::s -> ([Int] -> pin -> a -> State s b)
           -> LoopBody' pin (Array DIM0 a) (Array DIM0 b)
  -- the Bool signifies whether this is the last 'a'
  ManyToOne :: Int --insize
            -> s -> ([Int] -> pin ->
              a -> Bool -> State s (Maybe b))
            -> LoopBody' pin (Array DIM1 a) (Array DIM0 b)
  -- state seems fairly useless here, but for consistency
  OneToMany ::s -> ([Int] -> pin ->
              a -> State s [b])
            -> Int --outsize
            -> LoopBody' pin (Array DIM0 a) (Array DIM1 b)
  -- the Bool signifies whether this is the last 'a'
  ManyToMany :: Int --insize
             -> s -> ([Int] -> pin ->
               a -> Bool -> State s (Maybe b))
             -> Int --outsize
             -> LoopBody' pin (Array DIM1 a) (Array DIM1 b)

evalIR
  :: IntermediateRep pinputs () outputs
  -> Val pinputs
  -> Val outputs
evalIR ir input = undefined


evalIR'
  :: IntermediateRep pInputs tInputs outputs
  -> ValArr          pInputs
  -> ValArr                  tInputs'
  -> IdxSpaceTransform tInputs tInputs'
  -> IdxSpaceTransform outputs outputs'
  -> StateT [Int] IO (ValArr outputs') -- the [Int] is the current indices into the permanent inputs
evalIR' Void                  _    _    _   Id   = return EmptyEnv
--evalIR' (Id ir) (PushArr xs x) _ _ = (`PushArr` x) <$> evalIR' ir xs
evalIR' (For ir n ti' to') p t ti to = last <$> traverse (const $ evalIR' ir p t (compose ti' ti) (compose to' to)) [0..n-1] -- TODO adjust transform and use the i here
evalIR' (Before  body ir)  p t ti to = evalLoopBody body p t ti Id >>= \x -> evalIR' ir p x Id to
evalIR' (After   ir body)  p t ti to = evalIR' ir p t ti Id >>= \x -> evalLoopBody body p x Id to
evalIR' (Before' hf body ir)  p t ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to)
                                              a = evalLoopBody body p t ti tb in
    fuseHorizontal (unsafeCoerce hf) <$> a <*> (a >>= \x -> evalIR' ir p x tb tc) -- unsafeCoerce because we need the hf at the 'real' array level, not the phantom one
evalIR' (After'  hf ir body)  p t ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to)
                                              a = evalIR' ir p t ti tb in
    fuseHorizontal (unsafeCoerce hf) <$> a <*> (a >>= \x -> evalLoopBody body p x tb tc)
evalIR' (Besides hf body ir)  p t ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to) in
    fuseHorizontal (unsafeCoerce hf) <$> evalLoopBody body p t ti tb <*> evalIR' ir p t ti tc


-- the a', b' and c' should be the origins of a, b and c, so the two HF arguments should match
-- since this is always the case, we can unsafecoerce them? --TODO check
makeLeftIdx hf = makeLeftIdx' hf (unsafeCoerce hf)
makeRightIdx hf = makeRightIdx' hf (unsafeCoerce hf)

makeLeftIdx' :: HorizontalFusion a b c
             -> HorizontalFusion a' b' c'
             -> IdxSpaceTransform c c'
             -> IdxSpaceTransform a a'
makeLeftIdx' Done Done _ = Id
makeLeftIdx' (Righty r) (Righty r') _ = Id
makeLeftIdx' (Lefty l) (Lefty l') (Fn f x) = Fn f $ makeLeftIdx' l l' x
makeLeftIdx' _ _ _ = error "makeLeftIdx fusion arguments don't match"

makeRightIdx' :: HorizontalFusion a b c
              -> HorizontalFusion a' b' c'
              -> IdxSpaceTransform c c'
              -> IdxSpaceTransform b b'
makeRightIdx' Done Done _ = Id
makeRightIdx' (Righty r) (Righty r') (Fn f x) = Fn f $ makeRightIdx' r r' x
makeRightIdx' (Lefty l) (Lefty l') (Fn _ x) = makeRightIdx' l l' x
makeRightIdx' _ _ _ = error "makeRightIdx fusion arguments don't match"

evalLoopBody :: LoopBody pinputs tinputs outputs
             -> ValArr pinputs
             -> ValArr tinputs'
             -> IdxSpaceTransform tinputs tinputs'
             -> IdxSpaceTransform outputs outputs'
             -> StateT [Int] IO (ValArr outputs')
evalLoopBody = undefined

fuseHorizontal
  :: HorizontalFusion a b c
  -> ValArr a
  -> ValArr b
  -> ValArr c
fuseHorizontal Done _ _ = EmptyEnv
fuseHorizontal (Righty r) EmptyEnv (b `PushEnv` x) = PushEnv (fuseHorizontal r EmptyEnv b) x
fuseHorizontal (Lefty l) (a `PushEnv` x) b         = PushEnv (fuseHorizontal l a        b) x

