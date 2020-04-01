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
import           Unsafe.Coerce
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
import           Data.Array.Accelerate.Array.Data
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


data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e) => ValArr env -> Array sh e -> ValArr (env, Array sh e)

data Neg1 = Neg1

class ShapeIsh a
instance ShapeIsh Shape
instance ShapeIsh Neg1


data HorizontalFusion left right res where
  Done :: HorizontalFusion () () ()
  Righty :: HorizontalFusion () b b -> HorizontalFusion () (b, Array sh e) (b, Array sh e)
  Lefty  :: HorizontalFusion a  b c -> HorizontalFusion (a, Array sh e) b  (c, Array sh e)


data IdxSpaceTransform from to where
  Id :: IdxSpaceTransform a a
  Fn :: (Shape sh, Shape sh')
     => Int -- offset
     -> IdxSpaceTransform from to
     -> IdxSpaceTransform (from, Array sh e) (to, Array sh' e)

getCurrent :: IdxSpaceTransform (env, x) (env', x') -> Int
getCurrent Id = 0
getCurrent (Fn i _) = i

getRest :: IdxSpaceTransform (env, x) (env', x') -> IdxSpaceTransform env env'
getRest Id = Id
getRest (Fn _ x) = x

compose :: IdxSpaceTransform b c -> IdxSpaceTransform a b -> IdxSpaceTransform a c
compose Id x = x
compose x Id = x
compose (Fn i ab) (Fn j bc) = Fn (i+j) (compose ab bc)

infix 9 $*
($*) :: Int -> IdxSpaceTransform a b -> IdxSpaceTransform a b
_ $* Id = Id
i $* (Fn j f) = Fn (i*j) $ i $* f

-- transform :: IdxSpaceTransform (a, Array sh1 e) (b, Array sh2 e) -> Array sh1 e -> Array sh2 e
-- transform = undefined

inverse :: IdxSpaceTransform a b -> IdxSpaceTransform b a
inverse Id = Id
inverse (Fn i x) = Fn (-i) (inverse x)

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
  Simple :: LoopBody pin a b
         -> IntermediateRep pin a b

  -- Vertical fusion
  Before  :: LoopBody        pin a b
          -> IntermediateRep pin b c
          -> IntermediateRep pin a c
  After   :: IntermediateRep pin a b
          -> LoopBody        pin b c
          -> IntermediateRep pin a c

  -- Diagonal fusion
  Before' :: HorizontalFusion b c hor
          -> LoopBody        pin a b
          -> IntermediateRep pin b c
          -> IntermediateRep pin a hor
  After'  :: HorizontalFusion b c hor
          -> IntermediateRep pin a b
          -> LoopBody        pin b c
          -> IntermediateRep pin a hor

  -- Horizontal fusion
  Besides :: HorizontalFusion b c hor
          -> LoopBody        pin a b
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor

data LoopBody permIn tempIn out where
  Base :: LoopBody  pin () ()
  Take :: --(Shape sh1, Shape sh2, Elt a, Elt b)
        LoopBody' pin (Array sh1 a) (Array sh2 b)
       -> LoopBody  pin c d
       -> LoopBody  pin (c, Array sh1 a) (d, Array sh2 b)
  Drop :: LoopBody  pin a b
       -> LoopBody  pin (a,x) (b,x)


data LoopBody' permIn tempIn out where
  OneToOne :: (Elt a, Elt b)
           => IORef s
           -> (ValArr pin -> a -> State s b)
           -> LoopBody' pin (Array DIM0 a) (Array DIM0 b)
  ManyToOne :: (Elt a, Elt b)
            => Int
            -> IORef (s, Int)
            -> (ValArr pin -> a -> State s ())
            -> State s b
            -> LoopBody' pin (Array DIM0 a) (Array Neg1 b)
           {-
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
-}


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
evalIR' Void                 _ _ _ _  Id = return ()
evalIR' (For ir n ti' to')   p t o ti to = traverse_ (\i -> evalIR' ir p t o (i $* compose ti ti') (i $* compose to to')) [0..n-1]
evalIR' (Simple body)        p t o ti to = evalLoopBody body p t o ti to
evalIR' (Before  body ir)    p t o ti to = let temp = undefined in evalLoopBody body p t temp ti Id >> evalIR' ir p temp o Id to
evalIR' (After   ir body)    p t o ti to = let temp = undefined in evalIR' ir p t temp ti Id >> evalLoopBody body p temp o Id to
-- evalIR' (Before' hf body ir) p t o ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to)
--                                                a = evalLoopBody body p t ti tb in
--     fuseHorizontal (unsafeCoerce hf) <$> a <*> (a >>= \x -> evalIR' ir p x tb tc) -- unsafeCoerce because we need the hf at the 'real' array level, not the phantom one
-- evalIR' (After'  hf ir body) p t o ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to)
--                                                a = evalIR' ir p t ti tb in
--     fuseHorizontal (unsafeCoerce hf) <$> a <*> (a >>= \x -> evalLoopBody body p x tb tc)
-- evalIR' (Besides hf body ir) p t o ti to = let (tb, tc) = (makeLeftIdx hf to, makeRightIdx hf to) in
--     fuseHorizontal (unsafeCoerce hf) <$> evalLoopBody body p t ti tb <*> evalIR' ir p t ti tc

evalIR' _ _ _ _ _ _ = undefined -- TODO write the horizontal ones again



-- the a', b' and c' should be the origins of a, b and c, so the two HF arguments should match
-- since this is always the case, we can unsafecoerce them? --TODO check
makeLeftIdx :: HorizontalFusion a b c -> IdxSpaceTransform c c' -> IdxSpaceTransform a a'
makeLeftIdx hf = makeLeftIdx' hf (unsafeCoerce hf)
makeRightIdx :: HorizontalFusion a b c -> IdxSpaceTransform c c' -> IdxSpaceTransform b b'
makeRightIdx hf = makeRightIdx' hf (unsafeCoerce hf)



makeLeftIdx' :: HorizontalFusion a b c
             -> HorizontalFusion a' b' c'
             -> IdxSpaceTransform c c'
             -> IdxSpaceTransform a a'
makeLeftIdx' Done Done _ = Id
makeLeftIdx' (Righty _) (Righty _) _ = Id
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
             -> ValArr outputs'
             -> IdxSpaceTransform tinputs tinputs'
             -> IdxSpaceTransform outputs outputs'
             -> IO ()
evalLoopBody Base _ x y Id Id = assign Id x y

evalLoopBody (Drop     lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = assignArr         0     t o >> evalLoopBody lb p ts os Id Id
evalLoopBody (Drop     lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = assignArr         (-i)  t o >> evalLoopBody lb p ts os a  Id
evalLoopBody (Drop     lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = assignArr         j     t o >> evalLoopBody lb p ts os Id b
evalLoopBody (Drop     lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = assignArr         (i-j) t o >> evalLoopBody lb p ts os a  b
evalLoopBody (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = evalLoopBody' lb' 0 0 p t o >> evalLoopBody lb p ts os Id Id
evalLoopBody (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = evalLoopBody' lb' i 0 p t o >> evalLoopBody lb p ts os a  Id
evalLoopBody (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = evalLoopBody' lb' 0 j p t o >> evalLoopBody lb p ts os Id b
evalLoopBody (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = evalLoopBody' lb' i j p t o >> evalLoopBody lb p ts os a  b

evalLoopBody (Take _ _) _ EmptyEnv _ x _ = case x of {} -- There is no IdxSpaceTransform
evalLoopBody (Drop   _) _ EmptyEnv _ x _ = case x of {} -- possible for these cases,
evalLoopBody (Take _ _) _ _ EmptyEnv _ x = case x of {} -- so this satisfies GHC's
evalLoopBody (Drop   _) _ _ EmptyEnv _ x = case x of {} -- incomplete pattern check. :)



evalLoopBody' :: LoopBody' pinputs (Array sh1 e1) (Array sh2 e2)
              -> Int -- offset input  index
              -> Int -- offset output index
              -> ValArr pinputs
              -> Array sh1' e1
              -> Array sh2' e2
              -> IO ()
evalLoopBody' (OneToOne sref f) inoff outoff p (Array _ a) (Array _ b) = do
  s <- readIORef sref
  let (res, s') = (`runState` s) . f p . toElt $ unsafeIndexArrayData a inoff
  writeIORef sref s'
  unsafeWriteArrayData b outoff $ fromElt res

evalLoopBody' (ManyToOne n sref acc ret) inoff outoff p (Array _ a) (Array _ b) = do
  (s, i) <- readIORef sref
  let s' = (`execState` s) . acc p . toElt $ unsafeIndexArrayData a inoff
  let i' = i + 1
  writeIORef sref (s', i')
  when (i' == n) $ do
    let res = evalState ret s'
    unsafeWriteArrayData b outoff $ fromElt res



fuseHorizontal
  :: HorizontalFusion a b c
  -> ValArr a
  -> ValArr b
  -> ValArr c
fuseHorizontal Done _ _ = EmptyEnv
fuseHorizontal (Righty r) EmptyEnv (b `PushEnv` x) = PushEnv (fuseHorizontal r EmptyEnv b) x
fuseHorizontal (Lefty l) (a `PushEnv` x) b         = PushEnv (fuseHorizontal l a        b) x



-- assign the value 'from' to the internals of 'to'
assign :: IdxSpaceTransform a b -> ValArr a -> ValArr b -> IO ()
assign _ EmptyEnv EmptyEnv = return ()
assign Id       (PushEnv a from) (PushEnv b to) = assignArr 0 from to >> assign Id a b
assign (Fn i f) (PushEnv a from) (PushEnv b to) = assignArr i from to >> assign f  a b


-- TODO specialise if sh1 and sh2 match (and the offset is 0)
assignArr :: Int -> Array sh1 a -> Array sh2 a -> IO ()
assignArr = undefined -- TODO
