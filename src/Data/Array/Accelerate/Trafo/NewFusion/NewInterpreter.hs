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
-- {-# LANGUAGE EmptyCase              #-}
-- {-# LANGUAGE PartialTypeSignatures  #-} --todo maybe remove
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE StandaloneDeriving     #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-} -- making Neg1 an instance of these typeclasses is, in some cases, an ugly hack and not meaningful. You should never have an array element of type Neg1
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-} -- TODO remove
{-# OPTIONS_HADDOCK prune #-}


module Data.Array.Accelerate.Trafo.NewFusion.NewInterpreter (test) where

import System.IO.Unsafe

import           Control.Monad
import           Data.Typeable
import           Prelude                 hiding ( (!!)
                                                , sum
                                                )
import           Data.Array.Accelerate.Array.Data
import           Data.Array.Accelerate.Array.Sugar
-- import           Data.Array.Accelerate.Type
import Data.IORef
import           Control.Monad.State.Strict
import Data.Foldable
import Data.Type.Bool
import Data.Maybe
import Data.Array.Accelerate.Trafo.NewFusion.Neg1

data Exists' f where
  Exists' :: Typeable a => f a -> Exists' f

data ExistsArr where
  ExistsArr :: (Elt e, Shape sh) => Proxy (Array sh e) -> ExistsArr

data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e, Typeable env)
           => ValArr env
           -> Array sh e
           -> ValArr (env, Array sh e)
deriving instance Typeable ValArr
deriving instance Show (ValArr a)

data ValArr' env where
  ValArr' :: (Typeable env, Typeable env')
          => Transform env env'
          -> ValArr env'
          -> ValArr' env
deriving instance Show (ValArr' a)

-- This would be valid, if we didn't have the Typeable constraints
-- they are there for a reason though: we only want Transforms that work on tuplists of arrays.
-- instance Category Transform where
--   id = Id
--   (.) = compose

-- 'from' is a "subset" of 'to'
data Transform from to where
  Id :: Typeable a => Transform a a -- making this be "Transform () ()" would make more sense, but this allows for nice shortcuts when hand-writing transforms.
  Fn :: (Elt e, Shapeish sh, Shapeish sh', Typeable from, Typeable to)
  -- usually, sh' == sh :. Int. But due to composition it can be nested deeper,
  -- and we also say that Z "is equal to" Neg1 :. Int.
  -- Furthermore, in 'weakening' transforms, (Fn 0 _) is used as identity
     => Int -- offset: sh[0]==sh'[i]
     -> Transform from to
     -> Transform (from, Array sh e) (to, Array sh' e)
  Skip :: (Elt e, Shapeish sh, Typeable from, Typeable to)
       => Transform from to
       -> Transform from (to, Array sh e)
deriving instance Show (Transform a b)
deriving instance Eq (Transform a b)

-- doesn't have to strictly be a partition, probably?
--TODO specify: is the intersection always empty? Is the union always ab? Is it just two subsets?
-- Partitions inside of the IR should probably be strict partitions, and also not contain any (Fn i _) with i /= 0
data Partition a b ab = Partition (Transform a ab) (Transform b ab)

compose :: (Typeable a, Typeable b, Typeable c) => Transform b c -> Transform a b -> Transform a c
compose Id x = x
compose x Id = x
compose (Skip x) y = Skip (compose x y)
compose (Fn _ x) (Skip y) = Skip (compose x y)
compose (Fn i ab) (Fn j bc) = Fn (i+j) (compose ab bc)

($*) :: Int -> Transform a b -> Transform a b
_ $* Id = Id
i $* (Fn j f) = Fn (i*j) (i $* f)
i $* (Skip x) = Skip (i $* x)


--IR
data IntermediateRep permanentIn tempIn out where
  -- Basic control flow
  For  :: (Typeable tin, Typeable out, Typeable tin', Typeable out')
       => IntermediateRep pin tin out
       -> Int -- The number of times to loop
       -> Transform tin tin' -- These transforms should represent the offset of the second iteration,
       -> Transform out out' -- number 1, as they will get multiplied by the iteration counter
       -> IntermediateRep pin tin' out'
  Simple :: (Typeable a, Typeable b, Typeable x, Typeable y)
         => LoopBody pin a b x y
         -> IntermediateRep pin a b

  -- this Transform should only ever contain 'Fn 0 _' and "Skip _" and "Id",
  -- if it contains an index transform you should use 'For'.
  Weaken :: Typeable a
         => Transform a a'
         -> IntermediateRep p a  b
         -> IntermediateRep p a' b
  -- Vertical fusion
  Before  :: (Typeable a, Typeable b, Typeable ab)
          => Partition a b ab
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR (and should always be Z)
          -> LoopBody        pin a  b x 'True
          -> IntermediateRep pin ab c
          -> IntermediateRep pin a  c
  After   :: (Typeable a, Typeable b, Typeable ab)
          => Partition a b ab
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR (and should always be Z)
          -> IntermediateRep pin a  b
          -> LoopBody        pin ab c 'True x
          -> IntermediateRep pin a  c


  -- Diagonal fusion
  Before' :: (Typeable b, Typeable c)
          => Partition a b ab
          -> Partition b c hor
          -> LoopBody        pin a  b x 'True
          -> IntermediateRep pin ab c
          -> IntermediateRep pin a  hor
  After'  :: (Typeable b, Typeable c)
          => Partition a b ab
          -> Partition b c hor
          -> IntermediateRep pin a  b
          -> LoopBody        pin ab c 'True x
          -> IntermediateRep pin a  hor

  -- Horizontal fusion
  Besides :: (Typeable b, Typeable c)
          => Partition b c hor
          -> LoopBody        pin a b x y
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor
deriving instance Typeable IntermediateRep

--TODO replace with Idxs? also makes it easier to add zipwith..
data LoopBody permIn tempIn out fusein fuseout where
  Base :: LoopBody  pin () () 'True 'True
  Weak :: (Typeable a, Typeable b, Typeable a', Typeable b', Typeable rest)
       => Partition a rest a'
       -> Partition rest b b'
       -> LoopBody p a b fin fout
       -> LoopBody p a' b' fin fout
  Use  :: (Shape sh, Elt e, Typeable b) -- TODO only holds an index, should maybe add an (Int -> Int) argument
       => Array sh e
       -> IORef Int
       -> LoopBody pin a b fin fout
       -> LoopBody pin a (b, Array DIM0 e) fin fout
  Take :: (Shapeish sh1, Shapeish sh2, Elt a, Elt b, Typeable d)
       => LoopBody' pin (Array sh1 a) (Array sh2 b)
       -> LoopBody  pin c d fin fout
       -> LoopBody  pin (c, Array sh1 a)  (d, Array sh2 b) (fin && Canfuse sh1) (fout && Canfuse sh2)

-- arrays of dimension 'negative one' can't be fused vertically at that level, they have to be 'expanded' by a for-loop to dimension 0 first.
-- think of folds: fusing with their input happens one loop deeper than fusing with their output
-- note that arrays of dimension 'Neg1' can't actually exist, but we can create gadt's with a phantom type of 'Array Neg1 a', allowing us to 'IdxTransform' into it
type family Canfuse a = (b :: Bool) where
  Canfuse DIM0 = 'True
  Canfuse Neg1 = 'False

-- The 'State s' requirements allow functions to keep track of their running index into the permIn, which doesn't have idxtransforms
-- It also helps write Scans as 'OneToOne', and is essential to writing any meaningful (such as fold-like) 'ManyToOne'.
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


-- Represents the first part of normalise2', consisting of: xs, sum1, scn, and sum2.
testIR1 :: IO (IntermediateRep () () ((((), Array DIM1 Int), Array DIM0 Int), Array DIM0 Int))
testIR1 = do
  xs   <- newIORef 0 >>= \ref -> return $
    Use (fromList (Z:.30) [4..] :: Array DIM1 Int) ref Base
  sum1 <- newIORef (0, 0) >>= \ref -> return $
    Take (ManyToOne ref 30 (const $ modify . (+)) get) Base
  sum2 <- newIORef (0, 0) >>= \ref -> return $ Weaken (Fn 0 (Skip Id) :: Transform ((), Array DIM0 Int) (((), Array DIM0 Int), Array DIM0 Int)) $ Simple $
    Take (ManyToOne ref 30 (const $ modify . (+)) get) Base
  scn  <- newIORef 0      >>= \ref -> return $
    Take (OneToOne ref (const $ \a -> modify (+a) >> get)) Base
  temp <- PushEnv EmptyEnv . Array (fromElt Z) <$> newArrayData 1
  let sum2scn = Before (Partition (Skip Id) (Fn 0 (Skip Id))) temp scn sum2
  let sum1sum2scn = Besides (Partition (Skip Id :: Transform ((), Array Neg1 Int) (((), Array Neg1 Int), Array Neg1 Int)) (Fn 0 (Skip Id))) sum1 sum2scn
  let inner = Before' (Partition (Skip Id) Id) (Partition (Skip (Skip Id)) (Fn 0 (Fn 0 (Skip Id)))) xs sum1sum2scn :: IntermediateRep () () ((((), Array DIM0 Int), Array Neg1 Int), Array Neg1 Int)
  return $ For inner 30 Id (Fn 0 (Fn 0 (Fn 1 Id)))

test :: IO ()
test = do
  ir <- testIR1
  a <- Array (fromElt Z) <$> newArrayData 1
  b <- Array (fromElt Z) <$> newArrayData 1
  c <- Array (fromElt $ Z:.(30 :: Int)) <$> newArrayData 30
  let output = PushEnv (PushEnv (PushEnv EmptyEnv c) b) a
  evalIR ir EmptyEnv output
  print output


-- Evaluates the IR and stores the output in the provided mutable arrays
evalIR :: (Typeable pinputs, Typeable outputs)
       => IntermediateRep pinputs () outputs
       -> ValArr pinputs
       -> ValArr outputs
       -> IO ()
evalIR ir p o = evalIR' ir p (ValArr' Id EmptyEnv) (ValArr' Id o)



evalIR' :: (Typeable pInputs, Typeable tInputs, Typeable outputs)
        => IntermediateRep pInputs tInputs outputs   -- The instruction to execute. Contains recursive IR's (ir), LoopBodies (bdy), Transforms (ti', to', bh, ch), Temporary arrays (tmp)
        -> ValArr          pInputs                   -- The unfused inputs, p
        -> ValArr'                 tInputs           -- The   fused inputs, t
        -> ValArr'                         outputs   -- The         output, o
        -> IO ()
evalIR' (Simple bdy)       p t              o = evalLB bdy p t o
evalIR' (Weaken trans ir)  p (ValArr' ti t) o =
                      evalIR' ir p (ValArr' (compose ti trans) t) o
evalIR' (For ir n ti' to') p (ValArr' ti t) (ValArr' to o) =
  (`traverse_` [0..n-1]) $ \i ->
                  evalIR' ir p (ValArr' (compose ti (i $* ti')) t) (ValArr' (compose to (i $* to')) o)
evalIR' (Before pt@(Partition _ tb) b bdy ir) p t o              =
  case fuseEnvs pt t (ValArr' Id b) of
  ValArr' tc c -> evalLB bdy p t              (ValArr' (compose tc tb) c)
               >> evalIR' ir p (ValArr' tc c) o
evalIR' (After  pt@(Partition _ tb) b ir bdy) p t o              =
  case fuseEnvs pt t (ValArr' Id b) of
  ValArr' tc c -> evalIR' ir p t              (ValArr' (compose tc tb) c)
               >> evalLB bdy p (ValArr' tc c) o
evalIR' (Before' pt (Partition bh ch) bdy ir) p t (ValArr' to o) =
  case fuseEnvs pt t (ValArr' (compose to bh) o) of
  ValArr' tc c -> evalLB bdy p t              (ValArr' (compose to bh) o)
               >> evalIR' ir p (ValArr' tc c) (ValArr' (compose to ch) o)
evalIR' (After'  pt (Partition bh ch) ir bdy) p t (ValArr' to o) =
  case fuseEnvs pt t (ValArr' (compose to bh) o) of
  ValArr' tc c -> evalIR' ir p t              (ValArr' (compose to bh) o)
               >> evalLB bdy p (ValArr' tc c) (ValArr' (compose to ch) o)
evalIR' (Besides    (Partition bh ch) bdy ir) p t (ValArr' to o) =
                  evalLB bdy p t              (ValArr' (compose to bh) o)
               >> evalIR' ir p t              (ValArr' (compose to ch) o)


-- this function is honestly not pretty, but it doesn't quite translate nicely
-- into composition etc..
-- this function is a lot stricter than it needs to be, to assert some probable invariants: TODO check them to make sure
fuseEnvs :: Partition a b c -> ValArr' a -> ValArr' b -> ValArr' c
fuseEnvs (Partition Id _) a _ = a
fuseEnvs (Partition _ Id) _ b = b
fuseEnvs (Partition (Skip f) g@Fn{}) a (ValArr' h (PushEnv bs' b'))
  = case g of -- for some reason, you can't give as detailed type annotations in the top level patternmatch
    ((Fn 0 g') :: Transform (x, Array sh e) (y, Array sh' e))
      | Just Refl <- eqT @sh @sh' -> case h of
        Fn i tr -> case fuseEnvs (Partition f g') a (ValArr' tr bs') of
          ValArr' t x -> ValArr' (Fn i t) (PushEnv x b')
        Id      -> case fuseEnvs (Partition f g') a (ValArr' Id bs') of
          ValArr' t x -> ValArr' (Fn 0 t) (PushEnv x b')
        Skip tr -> fuseEnvs (Partition (Skip f) g) a (ValArr' tr bs')
    _ -> error "fuseEnvs, bc changes index"
fuseEnvs (Partition f@Fn{} g@Skip{}) a b = fuseEnvs (Partition g f) b a -- call the case above
fuseEnvs _ _ _ = error "fuseEnvs"

-- evaluate one iteration of a loopbody
evalLB :: Typeable tinputs
       => LoopBody pinputs tinputs outputs x y
       -> ValArr pinputs
       -> ValArr' tinputs
       -> ValArr' outputs
       -> IO ()
evalLB Base _ _ _ = return ()
evalLB (Weak (Partition aa' resta') (Partition restb' bb') lb) p (ValArr' ti t) (ValArr' to o) =
  copy (ValArr' (compose ti resta') t) (ValArr' (compose to restb') o)
  >> evalLB lb p (ValArr' (compose ti aa') t) (ValArr' (compose to bb') o)
  -- case fuseEnvs (Partition restb' bb') (ValArr' (compose ti resta') t) (ValArr' ) of
  -- _ -> _
-- Evaluate the LoopBody' and recurse
evalLB (Take lb' lb) p (ValArr' Id       (PushEnv ts t)) (ValArr' Id       (PushEnv os o)) = evalLB' lb' 0 0 p t o >> evalLB lb p (ValArr' Id ts) (ValArr' Id os)
evalLB (Take lb' lb) p (ValArr' (Fn i a) (PushEnv ts t)) (ValArr' Id       (PushEnv os o)) = evalLB' lb' i 0 p t o >> evalLB lb p (ValArr' a  ts) (ValArr' Id os)
evalLB (Take lb' lb) p (ValArr' Id       (PushEnv ts t)) (ValArr' (Fn j b) (PushEnv os o)) = evalLB' lb' 0 j p t o >> evalLB lb p (ValArr' Id ts) (ValArr' b  os)
evalLB (Take lb' lb) p (ValArr' (Fn i a) (PushEnv ts t)) (ValArr' (Fn j b) (PushEnv os o)) = evalLB' lb' i j p t o >> evalLB lb p (ValArr' a  ts) (ValArr' b  os)
-- copy the value from xs into the output (this is the only time we 'copy' array elements!)
evalLB (Use xs r lb) p (ValArr' ti                ts   ) (ValArr' Id       (PushEnv os o)) = readIORef r >>= \i -> modifyIORef r (+1) >> write xs o i 0 >> evalLB lb p (ValArr' ti ts) (ValArr' Id os)
evalLB (Use xs r lb) p (ValArr' ti                ts   ) (ValArr' (Fn j b) (PushEnv os o)) = readIORef r >>= \i -> modifyIORef r (+1) >> write xs o i j >> evalLB lb p (ValArr' ti ts) (ValArr' b os)
-- Recurse
evalLB lb p (ValArr' (Skip idxt) (PushEnv ts _)) (ValArr' idxo o) = evalLB lb p (ValArr' idxt ts) (ValArr' idxo  o)
evalLB lb p (ValArr' idxt t) (ValArr' (Skip idxo) (PushEnv os _)) = evalLB lb p (ValArr' idxt  t) (ValArr' idxo os)

-- write the 'inoff'-th element of 'from' to the 'outoff'-th element of 'to'
-- only called by evalLB, when a 'Use' brings an array into scope!
-- alternatively, 'Use' could also have been a constructor of the IR...
write :: Elt e => Array sh1 e -> Array sh2 e -> Int -> Int -> IO ()
write (Array _ from) (Array _ to) inoff outoff = do
  res <- unsafeReadArrayData from inoff
  unsafeWriteArrayData to outoff res

copy :: ValArr' a -> ValArr' a -> IO ()
copy (ValArr' (Skip x) (PushEnv y _)) z = copy (ValArr' x y) z
copy x (ValArr' (Skip y) (PushEnv z _)) = copy x (ValArr' y z)
copy (ValArr' ti@Fn{} i) (ValArr' to@Fn{} o)
  | (Fn 0 f :: Transform (a, Array sh e) (b, Array sh'  e)) <- ti
  , (Fn 0 g :: Transform (c, Array sh e) (d, Array sh'' e)) <- to
  , Just Refl <- eqT @sh' @sh'' = undefined i o f g -- TODO copy
  | otherwise = return () -- if the Fns are not 0, we're not in the first iteration of the loop so it will already have been copied
copy _ _ = undefined -- TODO, figure out whether we NEED a 'copy' function, whether it needs to be a computational waste (can we copy arrays, or does it need to be elementwise), and if it can be done array-wise, is the above attempt good enough?


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





-- The part below is an attempt at fusing arbitrary (fuseable) IRs, but it still needs some work

-- represents the first part of normalise2', consisting of: xs, sum1, scn, and sum2.
-- the second part (TODO) would consist of the rest: ys1, ys2 and the zipwith
testIR1' :: IO (IntermediateRep () () ((((), Array DIM1 Int), Array DIM0 Int), Array DIM0 Int))
testIR1' = fuseDiagonal <$>
            xs <*>
            (fuseHorizontal' <$>
              sum1 <*>
              join (fuseVertical <$>
                scn <*>
                sum2))
  where
    xs :: IO (IntermediateRep () () ((), Array DIM1 Int))
    xs = newIORef 0 >>= \ref -> return $
      For (Simple $ Use (fromList (Z:.30) [4..] :: Array DIM1 Int) ref Base) 30 Id trans
    sum1, sum2 :: IO (IntermediateRep () ((), Array DIM1 Int) ((), Array DIM0 Int))
    sum1 = newIORef (0, 0) >>= \ref -> return $
      For (Simple $ Take (ManyToOne ref 30 (const $ modify . (+)) get) Base) 30 trans trans'
    sum2 = sum1
    scn :: IO (IntermediateRep () ((), Array DIM1 Int) ((), Array DIM1 Int))
    scn = newIORef 0 >>= \ref -> return $
      For (Simple $ Take (OneToOne ref (const $ \a -> modify (+a) >> get)) Base) 30 trans trans
    trans :: Transform ((), Array DIM0 Int) ((), Array DIM1 Int)
    trans = Fn 1 Id
    trans' :: Transform ((), Array Neg1 Int) ((), Array DIM0 Int)
    trans' = Fn 0 Id

fuseHorizontal' :: forall p a b b' c c'. (Typeable a, Shapeish b, Shapeish c, Elt b', Elt c')
                => IntermediateRep p a ((),  Array b b')
                -> IntermediateRep p a ((),  Array c c')
                -> IntermediateRep p a (((), Array b b'), Array c c')
fuseHorizontal' b c = fuseHorizontal b c Id Id (Skip Id :: Transform ((), Array b b') (((), Array b b'), Array c c')) (Fn 0 (Skip Id))


-- notation: one ' is the left ir, two '' is the right ir, no ticks is the fused ir
-- a for inputs and b for outputs
-- "1" means it's the version inside of the FOR
-- where possible, transforms are named after their type variables:
-- (a1a1'' :: Transform a1'' a1)
fuseHorizontal :: forall p a a' a'' b b' b''.
                  (Typeable a, Typeable a', Typeable a'', Typeable b, Typeable b', Typeable b'')
               => IntermediateRep p a' b' -> IntermediateRep p a'' b'' -- The IR's to fuse
               -> Transform a' a -> Transform a'' a                    -- evidence that a', a'' ⊆ a
               -> Transform b' b -> Transform b'' b                    -- Evidence that b', b'' ⊆ b
               -> IntermediateRep p a b
fuseHorizontal (For bIR n'  ti'  to')
               (For cIR n'' ti'' to'')
               aa' aa'' bb' bb''
                | n' == n''
                = case   mkSmth aa' aa'' ti' ti'' of -- make the input Something
                  Exists'   (Something aa1 a1a1' a1a1'') ->
                    case mkSmth bb' bb'' to' to'' of -- make the output Something
                    Exists' (Something bb1 b1b1' b1b1'') ->
                      For (fuseHorizontal bIR cIR a1a1' a1a1'' b1b1' b1b1'') n' aa1 bb1
                | otherwise = error $ "fuseHorizontal, FOR loops don't match: "++ show n' ++ " " ++ show n''
fuseHorizontal (Weaken t ir1) ir2 aa' aa'' bb' bb'' = fuseHorizontal ir1 ir2 (compose aa' t) aa'' bb' bb''
fuseHorizontal ir1 (Weaken t ir2) aa' aa'' bb' bb'' = fuseHorizontal ir1 ir2 aa' (compose aa'' t) bb' bb''
fuseHorizontal (Simple lb) ir aa' aa'' bb' bb'' = Besides (Partition bb' bb'') (Weak (Partition aa'  mkSkips) trivialPartition lb) $ Weaken aa'' ir
fuseHorizontal ir (Simple lb) aa' aa'' bb' bb'' = Besides (Partition bb'' bb') (Weak (Partition aa'' mkSkips) trivialPartition lb) $ Weaken aa'  ir
fuseHorizontal (Before part b lb ir1) ir2 aa' aa'' bb' bb'' = case weakenPartition part aa' Id of
  Exists' (PartitionW (Partition t1 t2) t3) ->
    Before (Partition t1 t2) b (Weak (Partition aa'  mkSkips) trivialPartition lb) (fuseHorizontal ir1 ir2 t3 (compose t1 aa'') bb' bb'')
fuseHorizontal ir1 (Before part b lb ir2) aa' aa'' bb' bb'' = case weakenPartition part aa'' Id of
  Exists' (PartitionW (Partition t1 t2) t3) ->
    Before (Partition t1 t2) b (Weak (Partition aa'' mkSkips) trivialPartition lb) (fuseHorizontal ir1 ir2 (compose t1 aa')  t3 bb' bb'')
fuseHorizontal (After part b ir1 lb) ir2 aa' aa'' bb' bb'' = After _ (unsafePerformIO makeTemp) (fuseHorizontal ir1 ir2 aa' aa'' _ _) (Weak _ _ lb)
  --case weakenPartition part aa' Id of
--   Exists' (PartitionW (Partition t1 t2) t3) -> undefined
fuseHorizontal _ _ _ _ _ _ = undefined

data PartitionW a b ab a' b' ab' = PartitionW (Partition a' b' ab') (Transform ab ab')

weakenPartition :: forall a b ab a' b'. (Typeable a, Typeable b, Typeable ab, Typeable a', Typeable b')
                => Partition a b ab -> Transform a a' -> Transform b b' -> Exists' (PartitionW a b ab a' b')
weakenPartition (Partition Skip{} Skip{}) _ _ = error "two skips"
weakenPartition (Partition x'@Fn{} (Skip y)) Id g
  | (Fn i x :: Transform (from, Array sh e) (to, Array sh' e)) <- x' = case weakenPartition (Partition x y) Id g of
    Exists' (PartitionW (Partition l (r :: Transform b' ab')) w) -> Exists' (PartitionW (Partition (Fn i l :: Transform (from, Array sh e) (ab', Array sh' e)) (Skip r)) (Fn 0 w))
weakenPartition (Partition x'@Fn{} (Skip _)) f'@Fn{} _
  | (Fn i _ :: Transform (from, Array sh e) (to, Array sh' e)) <- x'
  , (Fn j _ :: Transform (from, Array sh e) (to2, Array sh'' e)) <- f'
  , i /= 0
  , j /= 0 = error $ "I don't know what to do here" ++ show i ++ show j
weakenPartition (Partition x'@Fn{} (Skip y)) f'@Fn{} g
  | (Fn i x :: Transform (from, Array sh e) (to, Array sh' e)) <- x'
  , (Fn j f :: Transform (from, Array sh e) (to2, Array sh'' e)) <- f'
  , j == 0 -- this case should probably be redundant, as it behaves the same as below if i=j=0 and j should always be 0?
  , Just Refl <- eqT @sh @sh'' = case weakenPartition (Partition x y) f g of
    Exists' (PartitionW (Partition l (r :: Transform b' ab')) w) -> Exists' (PartitionW (Partition (Fn j l :: Transform (to2, Array sh e) (ab', Array sh' e)) (Skip r)) (Fn i w))
weakenPartition (Partition x'@Fn{} (Skip y)) f'@Fn{} g
  | (Fn i x :: Transform (from, Array sh e) (to, Array sh' e)) <- x'
  , (Fn j f :: Transform (from, Array sh e) (to2, Array sh'' e)) <- f'
  , i == 0
  , Just Refl <- eqT @sh @sh' = case weakenPartition (Partition x y) f g of
    Exists' (PartitionW (Partition l (r :: Transform b' ab')) w) -> Exists' (PartitionW (Partition (Fn 0 l :: Transform (to2, Array sh'' e) (ab', Array sh'' e)) (Skip r)) (Fn j w :: Transform (to, Array sh e) (ab', Array sh'' e)))
weakenPartition (Partition (Fn i x) (Skip y)) f'@Skip{} g
  | (Skip f :: Transform from (to, Array sh e)) <- f' = case weakenPartition (Partition (Fn i x) (Skip y)) f g of
  Exists' (PartitionW (Partition l r) (w :: Transform ab ab')) -> Exists' $ PartitionW (Partition (Fn 0 l) (Skip r)) (Skip w :: Transform ab (ab', Array sh e))
weakenPartition (Partition Id y'@Skip{}) Id g
  | (Skip y :: Transform b (from, Array sh e)) <- y' = case weakenPartition (Partition Id y) Id g of
  Exists' (PartitionW (Partition l (r :: Transform b' ab')) w) -> Exists' $ PartitionW (Partition (Fn 0 l :: Transform (from, Array sh e) (ab', Array sh e)) (Skip r)) (Fn 0 w)
weakenPartition (Partition x@Skip{} y) f g = case weakenPartition (Partition y x) g f of -- mirror the above cases
  Exists' (PartitionW (Partition r l) w) -> Exists' (PartitionW (Partition l r) w)
weakenPartition _ _ _ = error "no skips"

-- used for horizontally fusing FOR loops. Notation matches 'fuseHorizontal', not 'mkSmth'. Note that some of the type variables are phantom.
data Something b' b'' b b1' b1'' b1 = Something (Transform b1 b) (Transform b1' b1) (Transform b1'' b1)

-- notation:
-- b is left, c is right, d is fused. Ticked type variables are the ones 'inside' of the FOR loop
-- in particular, the type d' is unkown and has multiple options. This function makes one, and the 'Something' to go with it.
mkSmth :: forall b c d b' c'. (Typeable b, Typeable c, Typeable d, Typeable b', Typeable c')
     => Transform b d -> Transform c d -> Transform b' b -> Transform c' c -> Exists' (Something b c d b' c')
mkSmth Id Id Id Id = Exists' $ Something Id Id Id -- trivial but probably irrelevant
mkSmth (Skip f) (Skip g) h i = case mkSmth f g h i of Exists' (Something x y z) -> Exists' $ Something (Skip x) y z
mkSmth (Skip f) (Fn x g) h asdf@Fn{} = case asdf of
  (Fn y i :: Transform (hi, Array sh e) (bye, Array sh' e)) -> case mkSmth f g h i of
    Exists' (Something a (b :: Transform from to) c) ->
      Exists' $ Something (Fn y a) (Skip b :: Transform from (to, Array sh e)) (Fn (x+y) c) --unsure about x+y? TODO test
  _ -> undefined -- clearly unreachable.. The awkward 'case asdf of' is needed to write the type annotation in the pattern
-- the symmetrical case of above
mkSmth (Fn x f) (Skip g) asdf@Fn{} i = case asdf of
  (Fn y h :: Transform (hi, Array sh e) (bye, Array sh' e)) -> case mkSmth f g h i of
    Exists' (Something a b (c :: Transform from to)) ->
      Exists' $ Something (Fn y a) (Fn (x+y) b) (Skip c :: Transform from (to, Array sh e))
  _ -> undefined
-- Same as before, but with 'Id' as 'Fn 0'
mkSmth (Skip f) Id h asdf@Fn{} = case asdf of
  (Fn y i :: Transform (hi, Array sh e) (bye, Array sh' e)) -> case mkSmth f Id h i of
    Exists' (Something a (b :: Transform from to) c) ->
      Exists' $ Something (Fn y a) (Skip b :: Transform from (to, Array sh e)) (Fn (0+y) c)
  _ -> undefined
-- the symmetrical case of above
mkSmth Id (Skip g) asdf@Fn{} i = case asdf of
  (Fn y h :: Transform (hi, Array sh e) (bye, Array sh' e)) -> case mkSmth Id g h i of
    Exists' (Something a b (c :: Transform from to)) ->
      Exists' $ Something (Fn y a) (Fn (0+y) b) (Skip c :: Transform from (to, Array sh e))
  _ -> undefined
mkSmth _ _ _ _ = undefined --TODO test a couple runs, I `think` these are all the patterns that should come up..


-- TODO
fuseDiagonal :: IntermediateRep p a b -> IntermediateRep p b (((),c),d) -> IntermediateRep p a ((b, c), d)
fuseDiagonal = undefined

-- this function is more restrictive than the IR, as can be seen from the type: the second IR cannot use the input of the first
-- TODO maybe generalise that, but it complicates this type signature and uses
fuseVertical :: forall p a b c. IntermediateRep p a b -> IntermediateRep p b c -> IO (IntermediateRep p a c)
fuseVertical (For (ir :: IntermediateRep p a' b') i ti _)
             (For (ir' :: IntermediateRep p b'' c') i' _ to')
              | i == i'
              , Just Refl <- eqT @b' @b''
                = (\x -> For x i ti to') <$> fuseVertical ir ir'
              | otherwise = error $ "vertical fusion of 'For " ++ show i ++ "' and 'For " ++ show i' ++ "'"

-- fuseVertical (Simple (lb :: LoopBody p a b x y)) ir
--   | Just Refl <- eqT @'True @y = (\t -> Before _ _ t lb (Weaken _ ir)) <$> makeTemp
--   | otherwise = error "verticalFusion"
-- fuseVertical ir (Simple (lb :: LoopBody p b c x y))
--   | Just Refl <- eqT @'True @x = (\t -> After  t ir lb) <$> makeTemp
--   | otherwise = error "verticalFusion"
fuseVertical _ _ = undefined -- TODO




data LBTransform a b ab = LBT (Transform a ab) (Transform b ab)

-- mkLBTransforms' :: (Typeable a, Typeable b, Typeable a', Typeable b')
--                 => LoopBody p a b x y
--                 -> Transform a a'
--                 -> Transform b b'
--                 -> Exists' (LBTransform a b)

-- see if this is even needed before updating it
-- mkLBTransforms :: (Typeable a, Typeable b) => LoopBody p a b x y -> Exists' (LBTransform a b)
-- mkLBTransforms Base         = Exists' $ LBT Id Id
-- mkLBTransforms (Weak f (Weak g lb)) = mkLBTransforms (Weak (compose f g) lb)
-- mkLBTransforms (Weak Id lb) = case mkLBTransforms lb of
--   Exists' (LBT a b) -> Exists' $ LBT a b
-- mkLBTransforms (Weak asdf@Skip{} lb) = case asdf of
--   (Skip f :: Transform from (to, Array sh e)) -> case mkLBTransforms (Weak f lb) of
--     Exists' (LBT (a :: Transform a' ab') b) ->
--       Exists' $ LBT (Fn 0 a :: Transform (a', Array sh e) (ab', Array sh e)) (Skip b)
--   _ -> undefined
-- mkLBTransforms (Weak t@(Fn 0 _) (Use (_ :: Array sh e) _ lb)) = case mkLBTransforms (Weak t lb) of
--   Exists' (LBT a b :: LBTransform a b ab) ->
--     Exists' $ LBT (Skip a) (Fn 0 b :: Transform (b, Array DIM0 e) (ab, Array DIM0 e))
-- mkLBTransforms (Weak f'@(Fn 0 _) (Take (_ :: LoopBody' p (Array sh1 e1) (Array sh2 e2)) lb)) =
--   case f' of
--   (Fn 0 f :: Transform (from, Array sh1' e1') (to, Array sh e)) ->
--     case eqT @(Array sh1 e1) @(Array sh1' e1') of -- has to be equal
--     Just Refl ->
--       case mkLBTransforms (Weak f lb) of
--       Exists' (LBT (a :: Transform froma toa) (b :: Transform fromb tob)) ->
--         Exists' $ LBT (Skip (Fn 0 a :: Transform (froma, Array sh e) (toa, Array sh e)) :: Transform (froma, Array sh e) ((toa, Array sh e), Array sh2 e2))
--                                          (Fn 0 (Skip b))
--     Nothing -> undefined
--   _ -> undefined
-- mkLBTransforms _ = undefined -- TODO finish

trivialPartition :: forall a. Typeable a => Partition () a a
trivialPartition = Partition mkSkips Id

mkSkips :: forall a. Typeable a => Transform () a
mkSkips = undefined -- TODO

makeTemp :: forall a. Typeable a => IO (ValArr a)
makeTemp = do
  exiEnv <- makeTemp' (typeRep (Proxy :: Proxy a))
  case exiEnv of -- forced to match on EmptyEnv and PushEnv to convince the typechecker of Typeable a; but the cases are identical
    Exists' EmptyEnv -> return . fromJust $ cast EmptyEnv -- fromJust is needed because makeTemp' gives no evidence that the ValArr is of the correct type, but we know it is.
    Exists' (PushEnv env arr) -> return . fromJust . cast $ PushEnv env arr

-- this is the real ugly part
makeTemp' :: TypeRep -> IO (Exists' ValArr)
makeTemp' typrep = case typeRepArgs typrep of
  [] -> return $ Exists' EmptyEnv
  [envrep, arrayTypeRep] -> do
    existsenv <- makeTemp' envrep
    case existsenv of
      Exists' env -> case typeRepArgs arrayTypeRep of
        [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
          then Exists' . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
          else error $ "Not a Z:" ++ show shaperep
        _ -> error "I'm a bad person"
  _ -> error "I'm a bad person"