{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE StandaloneDeriving     #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-} -- making Neg1 an instance of these typeclasses is, in some cases, an ugly hack and not meaningful. You should never have an array element of type Neg1
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-} -- TODO remove
{-# OPTIONS_HADDOCK prune #-}


module Data.Array.Accelerate.Trafo.NewFusion.NewInterpreter (test) where

import           Control.Monad
import           Data.Typeable
import           Prelude                 hiding ( (!!)
                                                , sum
                                                )
import           Data.Array.Accelerate.Array.Data
import           Data.Array.Accelerate.Array.Sugar
import           Data.Array.Accelerate.Type
import Data.IORef
import           Control.Monad.State.Strict
import Data.Foldable
import Data.Type.Bool
import Data.Maybe

data Exists' f where
  Exists' :: Typeable a => f a -> Exists' f

data ExistsArr where
  ExistsArr :: (Elt e, Shape sh) => Proxy (Array sh e) -> ExistsArr

data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e, Typeable env) => ValArr env -> Array sh e -> ValArr (env, Array sh e)
deriving instance Typeable ValArr
deriving instance Show (ValArr a)

--TODO refactor many places to use ValArr'
data ValArr' env where
  ValArr' :: (Typeable env, Typeable env')
    => Transform env env' -> ValArr env' -> ValArr' env
deriving instance Show (ValArr' a)

data Neg1 = Neg1 deriving (Show, Typeable)
instance ArrayElt Neg1 where
  type ArrayPtrs Neg1 = Neg1
instance Elt Neg1 where
  type EltRepr Neg1 = ()
  eltType       = TypeRunit
  fromElt Neg1   = ()
  toElt ()      = Neg1
class Elt a => ShapeIsh a where
  totalSize :: a -> Int
instance (Elt a, Shape a) => ShapeIsh a where
  totalSize = size
instance ShapeIsh Neg1 where
  totalSize _ = 1


-- 'from' is a "subset" of 'to'
data Transform from to where
  Id :: Typeable a => Transform a a -- making this be "Transform () ()" would make more sense, but this allows for nice shortcuts when hand-writing transforms.
  Fn :: (Elt e, ShapeIsh sh, ShapeIsh sh', Typeable from, Typeable to)
  -- usually, sh' == sh :. Int. But due to composition it can be nested deeper,
  -- and we also say that Z "is equal to" Neg1 :. Int.
  -- Furthermore, in 'weakening' transforms, (Fn 0) is used as identity
     => Int -- offset
     -> Transform from to
     -> Transform (from, Array sh e) (to, Array sh' e)
  Skip :: (Elt e, ShapeIsh sh, Typeable from, Typeable to)
       => Transform from to
       -> Transform from (to, Array sh e)
deriving instance Show (Transform a b)
deriving instance Eq (Transform a b)

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
          => Transform a ab -- only for weakening,
          -> Transform b ab -- no index transforms!
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR (and should always be Z)
          -> LoopBody        pin a  b x 'True
          -> IntermediateRep pin ab c
          -> IntermediateRep pin a  c
  After   :: Typeable b
          => Transform a ab -- only for weakening,
          -> Transform b ab -- no index transforms!
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR (and should always be Z)
          -> IntermediateRep pin a  b
          -> LoopBody        pin ab c 'True x
          -> IntermediateRep pin a  c


  -- Diagonal fusion
  Before' :: (Typeable b, Typeable c)
          => Transform a ab  -- only for
          -> Transform b ab  -- weakening,
          -> Transform b hor -- no index
          -> Transform c hor -- transforms!
          -> LoopBody        pin a  b x 'True
          -> IntermediateRep pin ab c
          -> IntermediateRep pin a  hor
  After'  :: (Typeable b, Typeable c)
          => Transform a ab  -- only for
          -> Transform b ab  -- weakening,
          -> Transform b hor -- no index
          -> Transform c hor -- transforms!
          -> IntermediateRep pin a  b
          -> LoopBody        pin ab c 'True x
          -> IntermediateRep pin a  hor

  -- Horizontal fusion
  Besides :: (Typeable b, Typeable c)
          => Transform b hor
          -> Transform c hor
          -> LoopBody        pin a b x y
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor
deriving instance Typeable IntermediateRep

data LoopBody permIn tempIn out fusein fuseout where
  Base :: LoopBody  pin () () 'True 'True
  Weak :: Typeable a
       => Transform a a'
       -> LoopBody p a  b fin fout
       -> LoopBody p a' b fin fout
  Use  :: (Shape sh, Elt e) -- TODO only holds an index, should maybe add an (Int -> Int) argument
       => Array sh e
       -> IORef Int
       -> LoopBody pin a b fin fout
       -> LoopBody pin a (b, Array DIM0 e) fin fout
  Take :: LoopBody' pin (Array sh1 a) (Array sh2 b)
       -> LoopBody  pin c d fin fout
       -> LoopBody  pin (c, Array sh1 a)  (d, Array sh2 b) (fin && Canfuse sh1) (fout && Canfuse sh2)

-- arrays of dimension 'negative one' can't be fused vertically at that level, they have to be 'expanded' by a for-loop to dimension 0 first.
-- think of folds: fusing with their input happens one loop deeper than fusing with their output
-- note that arrays of dimension 'Neg1' can't actually exist, but we can create gadt's with a phantom type of 'Array Neg1 a', allowing us to 'IdxTransform' into it
type family Canfuse a = (b :: Bool) where
  Canfuse DIM0 = 'True
  Canfuse Neg1 = 'False

-- The 'State s' requirements allow functions to keep track of their running index into the permIn, which doesn't have idxtransforms
-- It also helps write Scans as 'OneToOne', and is essential to writing any meaningful fold-like 'ManyToOne'.
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
  let sum2scn = Before (Skip Id) (Fn 0 (Skip Id)) temp scn sum2
  let sum1sum2scn = Besides (Skip Id :: Transform ((), Array Neg1 Int) (((), Array Neg1 Int), Array Neg1 Int)) (Fn 0 (Skip Id)) sum1 sum2scn
  let inner = Before' (Skip Id) Id (Skip (Skip Id)) (Fn 0 (Fn 0 (Skip Id))) xs sum1sum2scn :: IntermediateRep () () ((((), Array DIM0 Int), Array Neg1 Int), Array Neg1 Int)
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
evalIR ir p o = evalIR' ir p EmptyEnv o Id Id

evalIR' :: (Typeable pInputs, Typeable tInputs, Typeable outputs, Typeable tInputs', Typeable outputs')
        => IntermediateRep pInputs tInputs outputs   -- The instruction to execute. Contains recursive IR's (ir), LoopBodies (bdy), Transforms (ti', to', bh, ch), Temporary arrays (tmp)
        -> ValArr          pInputs                   -- The unfused inputs, p
        -> ValArr                  tInputs'          -- The   fused inputs, t
        -> ValArr                          outputs'  -- The         output, o
        -> Transform tInputs tInputs'                -- Transform   inputs, ti
        -> Transform outputs outputs'                -- Transform   output, to
        -> IO ()
evalIR' (Weaken trans ir)            p t o ti to = evalIR' ir p t o (compose ti trans) to
evalIR' (For ir n ti' to')           p t o ti to = (`traverse_` [0..n-1]) $ \i
                                                -> evalIR' ir p t o (compose ti (i $* ti')) (compose to (i $* to'))
evalIR' (Simple bdy)                 p t o ti to = evalLB bdy p t o ti to
evalIR' (Before  ta tb b bdy ir)     p t o ti to = case fuseEnvs ta tb (ValArr' ti t) (ValArr' Id b) of
                                   ValArr' tc c -> evalLB bdy p t c ti (compose tc tb)
                                                >> evalIR' ir p c o tc to
evalIR' (After   ta tb b ir bdy)     p t o ti to = case fuseEnvs ta tb (ValArr' ti t) (ValArr' Id b) of
                                   ValArr' tc c -> evalIR' ir p t c ti (compose tc tb)
                                                >> evalLB bdy p c o tc to
evalIR' (Before' ta tb bh ch bdy ir) p t o ti to = case fuseEnvs ta tb (ValArr' ti t) (ValArr' (compose to bh) o) of
                                   ValArr' tc c -> evalLB bdy p t o ti (compose to bh)
                                                >> evalIR' ir p c o tc (compose to ch)
evalIR' (After'  ta tb bh ch ir bdy) p t o ti to = case fuseEnvs ta tb (ValArr' ti t) (ValArr' (compose to bh) o) of
                                   ValArr' tc c -> evalIR' ir p t o ti (compose to bh)
                                                >> evalLB bdy p c o tc (compose to ch)
evalIR' (Besides bh ch bdy ir)       p t o ti to = evalLB bdy p t o ti (compose to bh)
                                                >> evalIR' ir p t o ti (compose to ch)

-- assumes that a and b are disjoint, and together make up c
-- this function is honestly not pretty, but it doesn't quite translate nicely
-- into composition etc..
-- this function is a lot stricter than it needs to be, to assert some probable invariants: TODO check them to make sure
fuseEnvs :: Transform a c -> Transform b c -> ValArr' a -> ValArr' b -> ValArr' c
fuseEnvs Id _ a _ = a
fuseEnvs _ Id _ b = b
fuseEnvs (Skip f) g@Fn{} a (ValArr' h (PushEnv bs' b'))
  = case g of -- for some reason, you can't give as detailed type annotations in the top level patternmatch
    ((Fn 0 g') :: Transform (x, Array sh e) (y, Array sh' e))
      | Just Refl <- eqT @sh @sh' -> case h of
        Fn i tr -> case fuseEnvs f g' a (ValArr' tr bs') of
          ValArr' t x -> ValArr' (Fn i t) (PushEnv x b')
        Id      -> case fuseEnvs f g' a (ValArr' Id bs') of
          ValArr' t x -> ValArr' (Fn 0 t) (PushEnv x b')
        Skip tr -> fuseEnvs (Skip f) g a (ValArr' tr bs')
    _ -> error "fuseEnvs, bc changes index"
fuseEnvs f@Fn{} g@Skip{} a b = fuseEnvs g f b a -- call the case above
fuseEnvs _ _ _ _ = error "fuseEnvs"


-- evaluate one iteration of a loopbody
evalLB :: (Typeable tinputs, Typeable tinputs')
       => LoopBody pinputs tinputs outputs x y
       -> ValArr pinputs
       -> ValArr tinputs'
       -> ValArr outputs'
       -> Transform tinputs tinputs'
       -> Transform outputs outputs'
       -> IO ()
evalLB Base _ _ _ Id Id = return ()
evalLB (Weak tr lb) p t o ti to = evalLB lb p t o (compose ti tr) to
-- Evaluate the LoopBody' and recurse
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = evalLB' lb' 0 0 p t o >> evalLB lb p ts os Id Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = evalLB' lb' i 0 p t o >> evalLB lb p ts os a  Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = evalLB' lb' 0 j p t o >> evalLB lb p ts os Id b
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = evalLB' lb' i j p t o >> evalLB lb p ts os a  b
-- copy the value from xs into the output (this is the only time we 'copy' array elements!)
evalLB (Use xs r lb) p ts             (PushEnv os o) ti       Id       = readIORef r >>= \i -> modifyIORef r (+1) >> write xs o i 0 >> evalLB lb p ts os ti Id
evalLB (Use xs r lb) p ts             (PushEnv os o) ti       (Fn j b) = readIORef r >>= \i -> modifyIORef r (+1) >> write xs o i j >> evalLB lb p ts os ti b
-- Recurse
evalLB lb p (PushEnv ts _) o (Skip idxt) idxo = evalLB lb p ts o idxt idxo
evalLB lb p t (PushEnv os _) idxt (Skip idxo) = evalLB lb p t os idxt idxo

                                              -- There is no Transform
evalLB Take{} _ EmptyEnv _ x _ = case x of {} -- possible for these cases,
evalLB Take{} _ _ EmptyEnv _ x = case x of {} -- so this satisfies GHC's
evalLB Use {} _ _ EmptyEnv _ x = case x of {} -- incomplete pattern check

-- write the 'inoff'-th element of 'from' to the 'outoff'-th element of 'to'
-- only called by evalLB, when a 'Use' brings an array into scope!
-- alternatively, 'Use' could also have been a constructor of the IR...
write :: Elt e => Array sh1 e -> Array sh2 e -> Int -> Int -> IO ()
write (Array _ from) (Array _ to) inoff outoff = do
  res <- unsafeReadArrayData from inoff
  unsafeWriteArrayData to outoff res

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
testIR1' = fuseDiagonal <$> xs <*> (fuseHorizontal' <$> sum1 <*> join (fuseVertical <$> scn <*> sum2))
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

fuseHorizontal' :: (Typeable a, Shape b, Shape c, Elt b', Elt c')
                => IntermediateRep p a ((),  Array b b')
                -> IntermediateRep p a ((),  Array c c')
                -> IntermediateRep p a (((), Array b b'), Array c c')
fuseHorizontal' b c = fuseHorizontal b c Id Id (Skip Id) (Fn 0 (Skip Id))


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
fuseHorizontal (Simple lb) ir aa' aa'' bb' bb'' = Besides bb' bb'' (Weak aa' lb) $ Weaken aa'' ir
fuseHorizontal ir (Simple lb) aa' aa'' bb' bb'' = Besides bb'' bb' (Weak aa'' lb) $ Weaken aa' ir
-- fuseHorizontal (Before ac bc b lb ir1) ir2 aa' aa'' bb' bb'' = _ (fuseHorizontal ir1 ir2 _ _ _ _)
-- fuseHorizontal ir1 (Before ac bc b lb ir2) aa' aa'' bb' bb'' = undefined -- Before ac bc b lb (fuseHorizontal (Weaken ac x) ir bd cd)
fuseHorizontal _ _ _ _ _ _ = undefined

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

mkLBTransforms :: LoopBody p a b x y -> Exists' (LBTransform a b)
mkLBTransforms Base         = Exists' $ LBT Id Id
mkLBTransforms (Weak Id lb) = case mkLBTransforms lb of
  Exists' (LBT a b) -> Exists' $ LBT a b
mkLBTransforms (Weak (Skip f) lb) = case mkLBTransforms (Weak f lb) of
  Exists' (LBT a b) -> undefined --Exists' $ LBT (Fn 0 a) (Skip b) --TODO add type applications to make this typecheck; and figure out how to handle (Fn 0 _) (can only be 0)



mkSkips :: forall a. Typeable a => Transform () a
mkSkips = undefined -- ugly to write



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
    case existsenv of -- forced to match on EmptyEnv and PushEnv to convince the typechecker of Typeable a; but the cases are identical
      Exists' env@EmptyEnv -> case typeRepArgs arrayTypeRep of
        [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
          then Exists' . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
          else error $ "Not a Z:" ++ show shaperep
        _ -> error "I'm a bad person"
      Exists' env@(PushEnv _ _) -> case typeRepArgs arrayTypeRep of
        [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
          then Exists' . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
          else error $ "Not a Z:" ++ show shaperep
        _ -> error "I'm a bad person"
  _ -> error "I'm a bad person"