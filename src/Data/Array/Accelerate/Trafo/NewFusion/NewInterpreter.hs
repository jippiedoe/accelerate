{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-unused-top-binds #-} -- TODO remove
{-# OPTIONS_HADDOCK prune #-}


module Data.Array.Accelerate.Trafo.NewFusion.NewInterpreter () where

import Data.Array.Accelerate.Trafo.NewFusion.Category
import Control.Monad
import Data.Typeable
import Prelude                 hiding ( (!!)
                                      , sum
                                      , (.)
                                      , id)
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST (Idx(..))
import Data.IORef
import Control.Monad.State.Strict
import Data.Foldable
import Data.Array.Accelerate.Trafo.NewFusion.Neg1



-- xs :: IntermediateRep ((), Vector Int) () ((), Vector Int)
-- xs = _ --TODO, rewrite example

-- sum1 :: IntermediateRep ((), Vector Int) ((), Vector Int) ((), Scalar Int)
-- sum1 = For (Simple $ Take (ManyToOne (const $ modify . (+)) get) Base) t1 t2

-- scn :: IntermediateRep ((), Vector Int) ((), Vector Int) ((), Vector Int)
-- scn = For (Simple $ Take (OneToOne (\_ a -> modify (+a) >> get)) Base) t1 t1

-- sum2 :: IntermediateRep ((), Vector Int) ((), Vector Int) ((), Scalar Int)
-- sum2 = sum1

-- t1 :: Transform ((), Scalar Int) ((), Vector Int)
-- t1 = Fn 1 Id
-- t2 :: Transform ((), Array Neg1 Int) ((), Scalar Int)
-- t2 = Fn 0 Id


class Environment env where
  consOrNull :: Either (env :~: ()) (ConsProof env)

data ConsProof env where
  CP :: (Shapeish sh, Elt e, Environment a) => (env :~: (a, Array sh e)) -> ConsProof env

instance Environment () where
  consOrNull = Left Refl

instance (Environment env, Shapeish sh, Elt e) => Environment (env, Array sh e) where
  consOrNull = Right $ CP Refl

data ExistsArr where
  ExistsArr :: (Elt e, Shape sh) => Proxy (Array sh e) -> ExistsArr

data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e)
           => ValArr env
           -> Array sh e
           -> ValArr (env, Array sh e)
deriving instance Show (ValArr a)

data ValArr' env where
  ValArr' :: (Environment env, Environment env')
          => Transform env env'
          -> ValArr env'
          -> ValArr' env
deriving instance Show (ValArr' a)

prj :: Idx env (Array sh e) -> ValArr env -> Array sh e
prj ZeroIdx (PushEnv _ v) = v
prj (SuccIdx idx) (PushEnv val _) = prj idx val

prj' :: Idx env (Array sh e) -> ValArr' env -> Array' e
prj' ZeroIdx (ValArr' (Fun i _) (PushEnv _ v)) = Array' i v
prj' (SuccIdx idx) (ValArr' (Fun _ tr) (PushEnv e _)) = prj' idx (ValArr' tr e)
prj' idx (ValArr' (Skp tr) (PushEnv e _)) = prj' idx (ValArr' tr e)
prj' idx (ValArr' Unt EmptyEnv) = case idx of {} -- no Idx possible, this convinces GHC


transform' :: Environment b => ValArr' a -> Transform b a -> ValArr' b
transform' (ValArr' x y) tr = ValArr' (x . tr) y

skip :: Environment env => ValArr' (env, a) -> ValArr' env
skip (ValArr' (Fun _ x) y) = ValArr' (Skp x) y
skip (ValArr' (Skp x) (PushEnv y z)) = case skip (ValArr' x y) of
  ValArr' a b -> ValArr' (Skp a) (PushEnv b z)

-- A reference to a part of a manifest array, which starts at the given index
data Array' a where
  Array' :: Int
         -> Array sh a
         -> Array' a


-- 'small' is a subset of 'big'
data Transform small big where
  Unt :: Transform () ()
  Fun :: (Elt e, Shapeish sh, Shapeish sh', Environment small, Environment big)
  -- usually, sh' == sh :. Int. But due to composition it can be nested deeper,
  -- and we also say that Z "is equal to" Neg1 :. Int.
  -- Furthermore, in 'weakening' transforms, (Fun 0 _) is used as identity
      => Int -- offset: sh[0]==sh'[i]
      -> Transform small big
      -> Transform (small, Array sh e) (big, Array sh' e)
  Skp :: (Elt e, Shapeish sh, Environment small, Environment big)
      => Transform small big
      -> Transform small (big, Array sh e)
deriving instance Show (Transform a b)
deriving instance Eq (Transform a b)

-- Transforms form a category over the set of Environments.
-- Note that this does not refer to Control.Category, but a version that allows us to specify the constraint
instance Category Transform where
  type Object Transform o = Environment o
  id = identity
  (.) = compose

identity :: forall a. Environment a => Transform a a
identity = case consOrNull @a of
  Left Refl -> Unt
  Right (CP Refl) -> Fun 0 identity

compose :: (Environment a, Environment b, Environment c)
        => Transform b c -> Transform a b -> Transform a c
compose Unt         Unt       = Unt
compose (Skp x)     y         = Skp (x . y)
compose (Fun _  x) (Skp y)    = Skp (x . y)
compose (Fun i bc) (Fun j ab) = Fun (i+j) (bc . ab)


-- doesn't have to strictly be a partition, probably?
--TODO specify: is the intersection always empty? Is the union always ab? Is it just two subsets?
-- Partitions inside of the IR should probably be strict partitions, and also not contain any (Fun i _) with i /= 0
data Partition a b ab where
  Partition :: (Environment a, Environment b, Environment ab) => Transform a ab -> Transform b ab -> Partition a b ab

skips :: forall env. Environment env => Transform () env
skips = case consOrNull @env of
  Left Refl -> Unt
  Right (CP Refl) -> Skp skips

onlyFirst :: (Environment rest, Environment env, Shapeish sh, Elt e)
          => Transform (rest, Array sh e) env -> Transform ((), Array sh e) env
onlyFirst (Fun i _) = Fun i skips
onlyFirst (Skp x) = Skp (onlyFirst x)

infixr 9 $*
($*) :: Int -> Transform a b -> Transform a b
_ $* Unt = Unt
i $* (Fun j f) = Fun (i*j) (i $* f)
i $* (Skp x) = Skp (i $* x)


-- idea: In all of IR, keep track of not only 'tempIn' and 'out', but the full environment that is needed for the computation.
-- for example: vertically fused (f :: a->b) and (g :: b -> c) has type (a -> c), but it needs an environment with a `b` in it.
-- that `b` can now be scalar, but still keep track of it. This removes a lot of complexity from the interpreter part!
-- IntermediateRep needs to now keep track of how the tempIn and out variables are a subset of the environment with transforms.
-- LoopBody can then finally just be an Idx based wrapper around a single LoopBody',
-- due to horizontal fusion we never needed LoopBody to hold multiple LoopBody' parts anyway.



data IntermediateRep perm temp input out where
  Simple :: LoopBody p t i o
         -> IntermediateRep p t i o

  -- Arrays in the environment that are not in i or o do not need to transform,
  -- as their bigger version is 'fused away': it can be mutated and reused
  For :: (Environment p, Environment t, Environment i, Environment i', Environment o, Environment o')
      => Transform i i'
      -> Transform o o'
      -> Int -- number of times to loop
      -> IntermediateRep p t i  o
      -> IntermediateRep p t i' o'

  -- Vertical
  -- the LoopBody has 'type' (i -> x), and the IR has 'type' ((i,x) -> o)
  Before :: (Environment p, Environment t, Environment i, Environment o, Shapeish sh, Elt x)
         => Transform x t
         -> LoopBody p t i x
         -> IntermediateRep p t x o
         -> IntermediateRep p t i o

  After :: (Environment p, Environment t, Environment i, Environment o, Shapeish sh, Elt x)
        => Transform x t
        -> IntermediateRep p t i x
        -> LoopBody p t x o
        -> IntermediateRep p t i o

data LoopBody perm temp input out where
  LB :: Partition i o t
     -> LoopBody'' p t i o
     -> LoopBody p t i o

data LoopBody'' perm temp input out where
  InOut :: (Shapeish sh1, Shapeish sh2, Elt i, Elt o, Environment ienv, Environment oenv)
        => Idx ienv (Array sh1 i)
        -> Idx oenv (Array sh2 o)
        -> LoopBody' p (Array sh1 i) (Array sh2 o)
        -> LoopBody'' p t ienv oenv
  InInOut :: (Shapeish sh1, Shapeish sh2, Elt i, Elt o, Environment ienv, Environment oenv)
          => Idx ienv (Array sh1 i1)
          -> Idx ienv (Array sh2 i2)
          -> Idx oenv (Array sh3 o)
          -> LoopBody2 p (Array sh1 i) (Array sh2 i2) (Array sh3 o)
          -> LoopBody'' p t ienv oenv


-- The 'State s' requirements allow functions to keep track of their running index into the permIn, which doesn't have idxtransforms
-- It also helps write Scans as 'OneToOne', and is essential to writing any meaningful (such as fold-like) 'ManyToOne'.
-- .. in other words, it's the cheat that makes these `parallel loops' sequential after all. This is the part that only works in the interpreter!
data LoopBody' permIn tempIn out where
  OneToOne :: (Elt a, Elt b)
           => IORef s
           -> (ValArr pin -> a -> State s b)
           -> LoopBody' pin (Scalar a) (Scalar b)
  ManyToOne :: (Elt a, Elt b)
            => IORef (s, Int)
            -> Int -- in size
            -> (ValArr pin -> a -> State s ())
            -> State s b
            -> LoopBody' pin (Scalar a) (Array Neg1 b)
  OneToMany :: (Elt a, Elt b)
            => IORef (s, [b], Int)
            -> Int -- out size
            -> (ValArr pin -> a -> State s [b])
            -> LoopBody' pin (Array Neg1 a) (Scalar b)

data LoopBody2 p i1 i2 o -- zips

-- fuseHorizontal :: Partition oL oR o
--                -> IntermediateRep p t i oL
--                -> IntermediateRep p t i oR
--                -> IntermediateRep p t i o

fuseVertical :: Partition i x ix
             -> IntermediateRep p t i  x
             -> IntermediateRep p t ix o
             -> IntermediateRep p t' i  o -- new t, TODO make existential wrapper
fuseVertical = undefined


evalIR :: (Environment p, Environment t, Environment i, Environment o) =>
          IntermediateRep p t i o
       -> ValArr p
       -> ValArr t
       -> Transform i i'
       -> Transform o o'
       -> IO ()
evalIR (For ii' oo' n ir) p t ii oo =
  (`traverse_` [0..n-1]) $ \i ->
    evalIR ir p t (ii . (i $* ii')) ((i $* oo') . oo)
evalIR (Simple lb)       p t ii oo = evalLB lb p t iot
evalIR (Before ixt lb ir) p t ii oo =
  evalLB lb p t (Partition it (onlyFirst ixt)) >> evalIR ir p t (Partition ixt ot)


evalLB'' :: LoopBody'' p t i o
         -> ValArr p
         -> ValArr t
         -> Partition i o t
         -> IO ()
evalLB'' (InOut idxi idxo lb') p t (Partition trI trO) = undefined
  -- evalLB'2 lb' p (prj' ZeroIdx (ValArr' trI t)) (prj' ZeroIdx (ValArr' trO t))


-- eventually, rewrite evalLB' to have this type. For now, this works
evalLB'2 :: LoopBody' p (Array sh1 e1) (Array sh2 e2)
         -> ValArr p
         -> Array' e1
         -> Array' e2
         -> IO ()
evalLB'2 lb' p (Array' i a1) (Array' j a2) = evalLB' lb' i j p a1 a2

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







-- -- this function is honestly not pretty, but it doesn't quite translate nicely
-- -- into composition etc..
-- -- this function is a lot stricter than it needs to be, to assert some probable invariants: TODO check them to make sure
-- fuseEnvs :: Partition a b c -> ValArr' a -> ValArr' b -> ValArr' c
-- fuseEnvs (Partition Unt _) a _ = a
-- fuseEnvs (Partition _ Id) _ b = b
-- fuseEnvs (Partition (Skip f) g@Fn{}) a (ValArr' h (PushEnv bs' b'))
--   = case g of -- for some reason, you can't give as detailed type annotations in the top level patternmatch
--     ((Fun 0 g') :: Transform (x, Array sh e) (y, Array sh' e))
--       | Just Refl <- eqT @sh @sh' -> case h of
--         Fun i tr -> case fuseEnvs (Partition f g') a (ValArr' tr bs') of
--           ValArr' t x -> ValArr' (Fun i t) (PushEnv x b')
--         Unt      -> case fuseEnvs (Partition f g') a (ValArr' Unt bs') of
--           ValArr' t x -> ValArr' (Fun 0 t) (PushEnv x b')
--         Skip tr -> fuseEnvs (Partition (Skip f) g) a (ValArr' tr bs')
--     _ -> error "fuseEnvs, bc changes index"
-- fuseEnvs (Partition f@Fn{} g@Skip{}) a b = fuseEnvs (Partition g f) b a -- call the case above
-- fuseEnvs _ _ _ = error "fuseEnvs"

-- data Exists' f where
--   Exists' :: Typeable a => f a -> Exists' f

-- makeTemp :: forall a. Typeable a => IO (ValArr a)
-- makeTemp = do
--   exiEnv <- makeTemp' (typeRep (Proxy :: Proxy a))
--   case exiEnv of -- forced to match on EmptyEnv and PushEnv to convince the typechecker of Typeable a; but the cases are identical
--     Exists' EmptyEnv -> return . fromJust $ cast EmptyEnv -- fromJust is needed because makeTemp' gives no evidence that the ValArr is of the correct type, but we know it is.
--     Exists' (PushEnv env arr) -> return . fromJust . cast $ PushEnv env arr

-- -- this is the real ugly part
-- makeTemp' :: TypeRep -> IO (Exists' ValArr)
-- makeTemp' typrep = case typeRepArgs typrep of
--   [] -> return $ Exists' EmptyEnv
--   [envrep, arrayTypeRep] -> do
--     existsenv <- makeTemp' envrep
--     case existsenv of
--       Exists' env -> case typeRepArgs arrayTypeRep of
--         [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
--           then Exists' . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
--           else error $ "Not a Z:" ++ show shaperep
--         _ -> error "I'm a bad person"
--   _ -> error "I'm a bad person"