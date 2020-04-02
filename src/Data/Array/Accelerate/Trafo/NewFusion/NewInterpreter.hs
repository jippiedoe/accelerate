{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -fno-warn-unused-top-binds #-} -- TODO remove
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
-- import           Control.Monad.ST
-- import           Data.Bits
-- import           Data.Char                      ( chr
--                                                 , ord
--                                                 )
-- import           Data.Primitive.ByteArray
-- import           Data.Primitive.Types
-- import           Data.Typeable
-- import           System.IO.Unsafe               ( unsafePerformIO )
-- import           Text.Printf                    ( printf )
-- import           Unsafe.Coerce
import           Prelude                 hiding ( (!!)
                                                , sum
                                                )
-- friends
-- import           Data.Array.Accelerate.Trafo.NewFusion.AST
--                                          hiding ( PreLabelledAcc(..) )

import           Data.Array.Accelerate.AST
                                         hiding ( Boundary
                                                , PreBoundary(..)
                                                , PreOpenAcc(..)
                                                )
-- import           Data.Array.Accelerate.Analysis.Type
--                                                 ( sizeOfScalarType
--                                                 , sizeOfSingleType
--                                                 )
import           Data.Array.Accelerate.Array.Data -- because we're doing a lot of mutating, and I'm paranoid, I try to avoid 'unsafeIndexArrayData' in favour of 'unsafeReadArrayData'
-- import qualified          Data.Array.Accelerate.Array.Representation
--                                                 ( SliceIndex(..) )
import           Data.Array.Accelerate.Array.Sugar
-- import           Data.Array.Accelerate.Error
-- import           Data.Array.Accelerate.Product
-- import           Data.Array.Accelerate.Type
-- import qualified Data.Array.Accelerate.AST     as AST
import qualified Data.Array.Accelerate.Smart   as Smart
import qualified Data.Array.Accelerate.Trafo   as AST

import Data.IORef
import           Control.Monad.State.Strict
import Data.Foldable
-- import Data.Array.Accelerate.Type
import Data.Type.Bool

data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e) => ValArr env -> Array sh e -> ValArr (env, Array sh e)

data Neg1 = Neg1

class ShapeIsh a
instance ShapeIsh Shape
instance ShapeIsh Neg1


-- data HorizontalFusion left right res where
--   Done :: HorizontalFusion () () ()
--   Righty :: HorizontalFusion () b b -> HorizontalFusion () (b, Array sh e) (b, Array sh e)
--   Lefty  :: HorizontalFusion a  b c -> HorizontalFusion (a, Array sh e) b  (c, Array sh e)

-- 'from' is a "subset" of 'to'
data IdxSpaceTransform from to where
  Id :: IdxSpaceTransform a a
  Fn :: (ShapeIsh sh, ShapeIsh sh')
     => Int -- offset
     -> IdxSpaceTransform from to
     -> IdxSpaceTransform (from, Array sh e) (to, Array sh' e) -- usually, sh' == sh :. Int. But due to composition it can be nested deeper, and we also say that Neg1 is a 'subset' of Z
  Skip :: ShapeIsh sh
       => IdxSpaceTransform from to
       -> IdxSpaceTransform from (to, Array sh e)



compose :: IdxSpaceTransform b c -> IdxSpaceTransform a b -> IdxSpaceTransform a c
compose Id x = x
compose x Id = x
compose (Skip x) y = Skip (compose x y)
compose (Fn _ x) (Skip y) = Skip (compose x y)
compose (Fn i ab) (Fn j bc) = Fn (i+j) (compose ab bc)

infix 9 $*
($*) :: Int -> IdxSpaceTransform a b -> IdxSpaceTransform a b
_ $* Id = Id
i $* (Fn j f) = Fn (i*j) (i $* f)
i $* (Skip x) = Skip (i $* x)


--IR
data IntermediateRep permanentIn tempIn out where
  Void :: IntermediateRep () () ()
  -- Id   ::(Elt e, Shape sh)
  --      => IntermediateRep a b
  --      -> IntermediateRep (a, Array sh e) (b, Array sh e)

  -- Basic control flow
  For  :: IntermediateRep pin tin out
       -> Int -- The number of times to loop
       -> IdxSpaceTransform tin tin' -- These IST's should represent the offset of the second iteration
       -> IdxSpaceTransform out out' -- (loop # 1), as they will get multiplied by the iteration counter
       -> IntermediateRep pin tin' out'
  Simple :: LoopBody pin a b x y
         -> IntermediateRep pin a b

  -- Vertical fusion
  Before  :: ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR
          -> LoopBody        pin a b x 'True
          -> IntermediateRep pin b c
          -> IntermediateRep pin a c
  After   :: ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR
          -> IntermediateRep pin a b
          -> LoopBody        pin b c 'True x
          -> IntermediateRep pin a c

  -- Diagonal fusion
  Before' :: IdxSpaceTransform b hor
          -> IdxSpaceTransform c hor
          -> LoopBody        pin a b x 'True
          -> IntermediateRep pin b c
          -> IntermediateRep pin a hor
  After'  :: IdxSpaceTransform b hor
          -> IdxSpaceTransform c hor
          -> IntermediateRep pin a b
          -> LoopBody        pin b c 'True x
          -> IntermediateRep pin a hor

  -- Horizontal fusion
  Besides :: IdxSpaceTransform b hor
          -> IdxSpaceTransform c hor
          -> LoopBody        pin a b x y
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor

data LoopBody permIn tempIn out fusein fuseout where
  Base :: LoopBody  pin () () 'True 'True
  Take :: LoopBody' pin (Array sh1 a) (Array sh2 b)
       -> LoopBody  pin c d fin fout
       -> LoopBody  pin (c, Array sh1 a) (d, Array sh2 b) (fin && Canfuse sh1) (fout && Canfuse sh2)
  Drop :: LoopBody  pin a b nfin fnout
       -> LoopBody  pin (a,x) (b,x) nfin nfout

-- arrays of dimension 'negative one' can't be fused vertically at that level, they have to be 'expanded' by a for-loop to dimension 0 first.
-- think of folds: fusing with their input happens one loop deeper than fusing with their output
-- note that arrays of dimension 'Neg1' can't actually exists, but we can create gadt's with a phantom type of 'Array Neg1 a', allowing us to 'IdxTransform' into it
type family Canfuse (a :: *) = (b :: Bool) where
  Canfuse DIM0 = 'True
  Canfuse Neg1 = 'False

-- the 'State s' requirements allow functions to keep track of their running index into the permIn, which doesn't have idxtransforms
data LoopBody' permIn tempIn out where
  OneToOne :: (Elt a, Elt b)
           => IORef s
           -> (ValArr pin -> a -> State s b)
           -> LoopBody' pin (Array DIM0 a) (Array DIM0 b)
  ManyToOne :: (Elt a, Elt b)
            => IORef (s, Int)
            -> Int -- in size
            -> (ValArr pin -> a -> State s ())
            -> State s b
            -> LoopBody' pin (Array DIM0 a) (Array Neg1 b)
  OneToMany :: (Elt a, Elt b)
            => IORef (s, [b], Int)
            -> Int -- out size
            -> (ValArr pin -> a -> State s [b])
            -> LoopBody' pin (Array Neg1 a) (Array DIM0 b)

            -- TODO to accomodate functions resulting from something like a 'unfold . fold', we need either this constructor (and a way to deal with it), or IntermediateRep needs to allow composition of two loops
            -- this generalisation might not be too common, but it SHOULD be allowed? Or is this an example of general composition inside of the outer loop, which is not the same as fusion across all dimensions?
            -- not even sure whether the ILP 'allows' this fusion
            -- there might be a way to allow IntermediateRep to contain two (or more?) loops inside of a loop while still statically avoiding non-fusion patterns?
            -- Or we just have to promise to avoid them when constructing the IR
  -- ManyToMany :: (Elt a, Elt b)
  --            => IORef s
  --            -> Int -- in size
  --            -> (pin -> a -> State s (Maybe b))
  --            -> Int -- out size
  --            -> LoopBody' pin (Array DIM1 a) (Array DIM1 b)



evalIR
  :: IntermediateRep pinputs () outputs
  -> Val pinputs
  -> Val outputs
evalIR = undefined


evalIR'
  :: IntermediateRep pInputs tInputs outputs
  -> ValArr          pInputs
  -> ValArr                  tInputs'
  -> ValArr                          outputs'
  -> IdxSpaceTransform tInputs tInputs'
  -> IdxSpaceTransform outputs outputs'
  -> IO ()
evalIR' Void                   _ _ _ _  _  = return ()
evalIR' (For ir n ti' to')     p t o ti to = traverse_ (\i -> evalIR' ir p t o (i $* compose ti ti') (i $* compose to to')) [0..n-1]
evalIR' (Simple bdy)           p t o ti to = evalLB bdy p t o ti to
evalIR' (Before  temp  bdy ir) p t o ti to = evalLB bdy p t temp ti Id >> evalIR' ir p temp o Id to
evalIR' (After   temp  ir bdy) p t o ti to = evalIR' ir p t temp ti Id >> evalLB bdy p temp o Id to
evalIR' (Before' bh ch bdy ir) p t o ti to = evalLB bdy p t o ti (compose to bh) >> evalIR' ir p o o (compose to bh) (compose to ch)
evalIR' (After'  bh ch ir bdy) p t o ti to = evalIR' ir p t o ti (compose to bh) >> evalLB bdy p o o (compose to bh) (compose to ch)
evalIR' (Besides bh ch bdy ir) p t o ti to = evalLB bdy p t o ti (compose to bh) >> evalIR' ir p t o ti (compose to ch)




evalLB :: LoopBody pinputs tinputs outputs x y
       -> ValArr pinputs
       -> ValArr tinputs'
       -> ValArr outputs'
       -> IdxSpaceTransform tinputs tinputs'
       -> IdxSpaceTransform outputs outputs'
       -> IO ()
evalLB Base _ x y Id Id = assign Id x y
-- Copy the top array, and recurse
evalLB (Drop     lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = assignArr   0     t o >> evalLB lb p ts os Id Id
evalLB (Drop     lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = assignArr   (-i)  t o >> evalLB lb p ts os a  Id
evalLB (Drop     lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = assignArr   j     t o >> evalLB lb p ts os Id b
evalLB (Drop     lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = assignArr   (i-j) t o >> evalLB lb p ts os a  b
-- Evaluate the LoopBody' and recurse
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = evalLB' lb' 0 0 p t o >> evalLB lb p ts os Id Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = evalLB' lb' i 0 p t o >> evalLB lb p ts os a  Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = evalLB' lb' 0 j p t o >> evalLB lb p ts os Id b
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = evalLB' lb' i j p t o >> evalLB lb p ts os a  b
-- Recurse
evalLB lb p (PushEnv ts _) o (Skip idxt) idxo = evalLB lb p ts o idxt idxo
evalLB lb p t (PushEnv os _) idxt (Skip idxo) = evalLB lb p t os idxt idxo

evalLB (Take _ _) _ EmptyEnv _ x _ = case x of {} -- There is no IdxSpaceTransform
evalLB (Drop   _) _ EmptyEnv _ x _ = case x of {} -- possible for these cases,
evalLB (Take _ _) _ _ EmptyEnv _ x = case x of {} -- so this satisfies GHC's
evalLB (Drop   _) _ _ EmptyEnv _ x = case x of {} -- incomplete pattern check. :)



evalLB' :: LoopBody' pinputs (Array sh1 e1) (Array sh2 e2)
              -> Int -- offset input  index
              -> Int -- offset output index
              -> ValArr pinputs
              -> Array sh1' e1
              -> Array sh2' e2
              -> IO ()
evalLB' (OneToOne sref f) inoff outoff p (Array _ a) (Array _ b) = do
  s <- readIORef sref
  a' <- unsafeReadArrayData a inoff
  let (res, s') = (`runState` s) . f p . toElt $ a'
  writeIORef sref s'
  unsafeWriteArrayData b outoff $ fromElt res

evalLB' (ManyToOne sref n acc ret) inoff outoff p (Array _ a) (Array _ b) = do
  (s, i) <- readIORef sref
  a' <- unsafeReadArrayData a inoff
  let s' = (`execState` s) . acc p . toElt $ a'
  let i' = (i + 1) `mod` n
  writeIORef sref (s', i')
  when (i' == 0) $ do
    let res = evalState ret s'
    unsafeWriteArrayData b outoff $ fromElt res

evalLB' (OneToMany sref n f) inoff outoff p (Array _ a) (Array _ b) = do
  (s', bs', i) <- readIORef sref
  (bs, s) <- if i==0 then do
    a' <- unsafeReadArrayData a inoff
    return . (`runState` s') . f p . toElt $ a'
      else return (bs', s')
  let i' = (i+1) `mod` n
  writeIORef sref (s, tail bs, i')
  unsafeWriteArrayData b outoff . fromElt . head $ bs


-- assign the value 'from' to the internals of 'to'
assign :: IdxSpaceTransform a b -> ValArr a -> ValArr b -> IO ()
assign Id EmptyEnv EmptyEnv = return ()
assign Id       (PushEnv a from) (PushEnv b to) = assignArr 0 from to >> assign Id a b
assign (Fn i f) (PushEnv a from) (PushEnv b to) = assignArr i from to >> assign f  a b
assign (Skip f) a (PushEnv b _) = assign f a b

-- TODO specialise if sh1 and sh2 match (and the offset is 0)
assignArr :: Int -> Array sh1 a -> Array sh2 a -> IO ()
assignArr = undefined -- TODO
