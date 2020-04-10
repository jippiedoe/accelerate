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
import           Data.Typeable
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
-- import qualified          Data.Array.Accelerate.Array.Representation as Repr
--                                                 ( SliceIndex(..) )
import           Data.Array.Accelerate.Array.Sugar
-- import           Data.Array.Accelerate.Error
-- import           Data.Array.Accelerate.Product
import           Data.Array.Accelerate.Type
-- import qualified Data.Array.Accelerate.AST     as AST
import qualified Data.Array.Accelerate.Smart   as Smart
import qualified Data.Array.Accelerate.Trafo   as AST

import Data.IORef
import           Control.Monad.State.Strict
import Data.Foldable
-- import Data.Array.Accelerate.Type
import Data.Type.Bool

-- import Data.Array.Accelerate.Analysis.Match

-- import Unsafe.Coerce
import Data.Maybe




data Exists' f where
  Exists' :: Typeable a => f a -> Exists' f

data ExistsArr where
  ExistsArr :: (Elt e, Shape sh) => Proxy (Array sh e) -> ExistsArr

data ValArr env where
  EmptyEnv :: ValArr ()
  PushEnv  :: (Shape sh, Elt e, Typeable env) => ValArr env -> Array sh e -> ValArr (env, Array sh e)
deriving instance Typeable ValArr

--TODO refactor many other places to use ValArr' :)
data ValArr' env where
  ValArr' :: (Typeable env, Typeable env')
    => Transform env env' -> ValArr env' -> ValArr' env

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
  Id :: Typeable a => Transform a a
  Fn :: (ShapeIsh sh, Shape sh', Typeable from, Typeable to)
     => Int -- offset
     -> Transform from to
     -> Transform (from, Array sh e) (to, Array sh' e) -- usually, sh' == sh :. Int. But due to composition it can be nested deeper, and we also say that Neg1 is a 'subset' of Z
  Skip :: (Elt e, ShapeIsh sh, Typeable from, Typeable to)
       => Transform from to
       -> Transform from (to, Array sh e)

deriving instance Show (Transform a b)
deriving instance Eq (Transform a b)

-- compareTransform :: Transform a b -> Transform c b -> Maybe (a :~: c)
-- compareTransform (Skip f) (Skip g) = compareTransform f g
-- compareTransform Id Id = Just Refl
-- compareTransform (Fn i f) (Fn j g) =

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
  Void :: IntermediateRep pin () ()
  -- Id   ::(Elt e, Shape sh)
  --      => IntermediateRep a b
  --      -> IntermediateRep (a, Array sh e) (b, Array sh e)
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


    -- TODO: Before and Before' need an adjustment:
    --       The IR should have access to the input of the LB too.
    --       This would put it in line with the newfusion.AST vertical/diagonal concepts,
    --       and allow horizontally fusing these constructs.
    --       perhaps even After and After' should incorporate this,
    --       allowing the LB to have access to the input of the IR.

  -- Vertical fusion
  Before  :: (Typeable a, Typeable b)
          => Transform a c -- only for weakening,
          -> Transform b c -- no index transforms!
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR
          -> LoopBody        pin a b x 'True
          -> IntermediateRep pin c d
          -> IntermediateRep pin a d
  After   :: Typeable b
          => Transform a c -- only for weakening,
          -> Transform b c -- no index transforms!
          -> ValArr b -- temporary result allocation place, the dimensions (concrete shapes) should be computable while constructing this IR
          -> IntermediateRep pin a b
          -> LoopBody        pin c d 'True x
          -> IntermediateRep pin a d


  -- Diagonal fusion
  Before' :: (Typeable b, Typeable c)
          => Transform b hor
          -> Transform c hor
          -> LoopBody        pin a b x 'True
          -> IntermediateRep pin b c
          -> IntermediateRep pin a hor
  After'  :: (Typeable b, Typeable c)
          => Transform b hor
          -> Transform c hor
          -> IntermediateRep pin a b
          -> LoopBody        pin b c 'True x
          -> IntermediateRep pin a hor

  -- Horizontal fusion
  Besides :: (Typeable b, Typeable c)
          => Transform b hor
          -> Transform c hor
          -> LoopBody        pin a b x y
          -> IntermediateRep pin a c
          -> IntermediateRep pin a hor
deriving instance Typeable IntermediateRep

data LoopBody permIn tempIn out fusein fuseout where
  Use :: (Shape sh, Elt e) -- TODO only holds an index, should maybe add an (Int -> Int) argument
      => Array sh e
      -> IORef Int
      -> LoopBody pin a b fin fout
      -> LoopBody pin a (b, Array DIM0 e) fin fout
  Base :: LoopBody  pin () () 'True 'True
  Take :: LoopBody' pin (Array sh1 a) (Array sh2 b)
       -> LoopBody  pin c d fin fout
       -> LoopBody  pin (c, Array sh1 a)  (d,               Array sh2 b) (fin && Canfuse sh1) (fout && Canfuse sh2)
  -- Give :: LoopBody' pin (Array sh1 a) (Array sh2 b)
  --      -> LoopBody  pin c d fin fout
  --      -> LoopBody  pin (c, Array sh1 a) ((d, Array sh1 a), Array sh2 b) (fin && Canfuse sh1) (fout && Canfuse sh2)


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


  -- TODO to accomodate functions resulting from something like a 'unfold . fold', we need either this constructor (and a way to deal with it), or IntermediateRep needs to allow composition of two loops
  -- this generalisation might not be too common, but it SHOULD be allowed? Or is this an example of general composition inside of the outer loop, which is not the same as fusion across all dimensions?
  -- not even sure whether the ILP 'allows' this fusion
  -- note that 'fold . unfold' can already be expressed!

  -- there might be a way to allow IntermediateRep to contain two (or more?) loops inside of a loop while still statically avoiding non-fusion patterns?
  -- Or we just have to promise to avoid them when constructing the IR
  -- but maybe having non-nested loops is by definition a non-fused pattern

  -- ManyToMany :: (Elt a, Elt b)
  --            => IORef s
  --            -> Int -- in size
  --            -> (pin -> a -> State s (Maybe b))
  --            -> Int -- out size
  --            -> LoopBody' pin (Array DIM1 a) (Array DIM1 b)






-- represents the first part of normalise2', consisting of: xs, sum1, scn, and sum2.
-- the second part (TODO) would consist of the rest: ys1, ys2 and the zipwith
testIR1 :: IO (IntermediateRep () () ((((), Array DIM1 Int), Array DIM0 Int), Array DIM0 Int))
testIR1 = fuseDiagonal <$> xs <*> (fuseHorizontal' <$> sum1 <*> join (fuseVertical <$> scn <*> sum2))
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

fuseHorizontal' :: (Shape b, Shape c, Elt b', Elt c')
                => IntermediateRep p a ((), Array b b')
                -> IntermediateRep p a ((), Array c c')
                -> IntermediateRep p a (((), Array b b'), Array c c')
fuseHorizontal' b c = fuseHorizontal b c (Skip Id) (Fn 0 (Skip Id))


fuseHorizontal :: forall p a b c d. (Typeable b, Typeable c, Typeable d)
                => IntermediateRep p a b -> IntermediateRep p a c -- The IR's to fuse
                -> Transform b d -> Transform c d                 -- Evidence that b,c ⊆ d
                -> IntermediateRep p a d
fuseHorizontal (For (bIR :: IntermediateRep p a' b')  bn ib ob)
               (For (cIR :: IntermediateRep p a'' c') cn ic oc)
               bd cd | bn == cn                  -- Ensure that the
                     , Just Refl <- eqT @a' @a'' --  'For loops'
                     , ib == ic                  --  are fusable
                = case mkSmth bd cd ob oc of
                  Exists' (Something dd bd' cd') ->
                    For (fuseHorizontal bIR cIR bd' cd') bn ib dd
                | otherwise = error "fuseHorizontal, FOR loops don't match"
fuseHorizontal (Simple lb) ir bd cd = Besides bd cd lb ir
fuseHorizontal ir (Simple lb) bd cd = Besides cd bd lb ir
fuseHorizontal (Before ac bc b lb ir) y bd cd = Before ac bc b lb (fuseHorizontal ir (Weaken ac y) bd cd)
fuseHorizontal x (Before ac bc b lb ir) bd cd = Before ac bc b lb (fuseHorizontal (Weaken ac x) ir bd cd)

fuseHorizontal Void x _ Id = x
fuseHorizontal Void _ _ _ = error "unreachable? I guess so"
fuseHorizontal x Void Id _ = x
fuseHorizontal _ Void _ _ = error "unreachable? I guess so"

fuseHorizontal _ _ _ _ = undefined

data Something b c d b' c' d' = Something (Transform d' d) (Transform b' d') (Transform c' d')

mkSmth :: forall b c d b' c'. (Typeable b, Typeable c, Typeable d, Typeable b', Typeable c')
     => Transform b d -> Transform c d -> Transform b' b -> Transform c' c -> Exists' (Something b c d b' c')
mkSmth Id Id Id Id = Exists' $ Something Id Id Id
mkSmth (Skip f) (Skip g) h i = case mkSmth f g h i of Exists' (Something x y z) -> Exists' $ Something (Skip x) y z
mkSmth (Skip (f :: Transform b smth)) (Fn a g) h (Fn b i) = case undefined of --TODO replace these undefined's
  ExistsArr (Proxy :: Proxy (Array sh e)) -> case undefined of
    (Refl :: (d :~: (smth, Array sh e))) -> case mkSmth f g h i of
      Exists' (Something (x :: Transform smalld' smalld) y z) -> Exists' $ Something (Fn b x :: Transform (smalld', Array sh e) d) (Skip y) (Fn a z)
mkSmth _ _ _ _ = undefined --TODO this should be possible, it's just a pain to write

-- TODO generalise type
fuseDiagonal :: IntermediateRep p a b -> IntermediateRep p b (((),c),d) -> IntermediateRep p a ((b, c), d)
fuseDiagonal = undefined

fuseVertical :: forall p a b c. IntermediateRep p a b -> IntermediateRep p b c -> IO (IntermediateRep p a c)
fuseVertical Void a = return a
fuseVertical (For (ir :: IntermediateRep p a' b') i ti _)
             (For (ir' :: IntermediateRep p b'' c') i' _ to')
              | i == i'
              , Just Refl <- eqT @b' @b''
                = (\x -> For x i ti to') <$> fuseVertical ir ir'
              | otherwise = error $ "vertical fusion of 'For " ++ show i ++ "' and 'For " ++ show i' ++ "'"
--TODO weaken 'ir'
-- fuseVertical (Simple (lb :: LoopBody p a b x y)) ir
--   | Just Refl <- eqT @'True @y = (\t -> Before t lb ir) <$> makeTemp
--   | otherwise = error "verticalFusion"
-- fuseVertical ir (Simple (lb :: LoopBody p b c x y))
--   | Just Refl <- eqT @'True @x = (\t -> After  t ir lb) <$> makeTemp
--   | otherwise = error "verticalFusion"
fuseVertical _ _ = undefined -- TODO

makeTemp :: forall a. Typeable a => IO (ValArr a)
makeTemp = do
  exiEnv <- makeTemp' (typeRep (Proxy :: Proxy a))
  case exiEnv of -- forced to match on EmptyEnv and PushEnv to convince the typechecker of Typeable a; but the cases are identical
    Exists EmptyEnv -> return . fromJust $ cast EmptyEnv -- fromJust is needed because makeTemp' gives no evidence that the ValArr is of the correct type, but we know it is.
    Exists (PushEnv env arr) -> return . fromJust . cast $ PushEnv env arr

makeTemp' :: TypeRep -> IO (Exists ValArr)
makeTemp' typrep = case typeRepArgs typrep of
  [] -> return $ Exists EmptyEnv
  [envrep, arrayTypeRep] -> do
    existsenv <- makeTemp' envrep
    case existsenv of -- forced to match on EmptyEnv and PushEnv to convince the typechecker of Typeable a; but the cases are identical
      Exists env@EmptyEnv -> case typeRepArgs arrayTypeRep of
        [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
          then Exists . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
          else error $ "Not a Z:" ++ show shaperep
        _ -> error "I'm a bad person"
      Exists env@(PushEnv _ _) -> case typeRepArgs arrayTypeRep of
        [shaperep, _] -> if shaperep == typeRep (Proxy :: Proxy Z) --TODO check for other elt types
          then Exists . PushEnv env <$> ((Array (fromElt Z) <$> newArrayData 1) :: IO (Array Z Int))
          else error $ "Not a Z:" ++ show shaperep
        _ -> error "I'm a bad person"
  _ -> error "I'm a bad person"




evalIR :: IntermediateRep pinputs () outputs
       -> Val pinputs
       -> Val outputs
evalIR = undefined

-- Evaluates the IR and stores the output in the provided mutable arrays
evalIR' :: (Typeable pInputs, Typeable tInputs, Typeable outputs, Typeable tInputs', Typeable outputs')
        => IntermediateRep pInputs tInputs outputs   -- The instruction to execute. Contains recursive IR's (ir), LoopBodies (bdy), Transforms (ti', to', bh, ch), Temporary arrays (tmp)
        -> ValArr          pInputs                   -- The unfused inputs, p
        -> ValArr                  tInputs'          -- The   fused inputs, t
        -> ValArr                          outputs'  -- The         output, 0
        -> Transform tInputs tInputs'                -- Transform   inputs, ti
        -> Transform outputs outputs'                -- Transform   output, to
        -> IO ()
evalIR' Void                    _ _ _ _  _  = return ()
evalIR' (Weaken trans ir)       p t o ti to = evalIR' ir p t o (compose ti trans) to
evalIR' (For ir n ti' to')      p t o ti to = traverse_ (\i -> evalIR' ir p t o (compose ti (i $* ti')) (compose to (i $* to'))) [0..n-1] -- each iteration, multiply the added transform by the iteration counter
evalIR' (Simple bdy)            p t o ti to = evalLB bdy p t o ti to
evalIR' (Before ac bc b bdy ir) p t o ti to = case fuseEnvs ac bc (ValArr' ti t) b of
                              ValArr' tc c -> evalLB bdy p t c ti (compose tc bc) >> evalIR' ir p c o tc              to
evalIR' (After  ac bc b ir bdy) p t o ti to = case fuseEnvs ac bc (ValArr' ti t) b of
                              ValArr' tc c -> evalIR' ir p t c ti (compose tc bc) >> evalLB bdy p c o tc              to
evalIR' (Before' bh ch bdy ir)  p t o ti to = evalLB bdy p t o ti (compose to bh) >> evalIR' ir p o o (compose to bh) (compose to ch)
evalIR' (After'  bh ch ir bdy)  p t o ti to = evalIR' ir p t o ti (compose to bh) >> evalLB bdy p o o (compose to bh) (compose to ch)
evalIR' (Besides bh ch bdy ir)  p t o ti to = evalLB bdy p t o ti (compose to bh) >> evalIR' ir p t o ti              (compose to ch)

-- assumes that a and b are disjoint, and together make up c
fuseEnvs :: Transform a c -> Transform b c -> ValArr' a -> ValArr b -> ValArr' c
fuseEnvs Id _ a _ = a
fuseEnvs _ Id _ b = ValArr' Id b
fuseEnvs (Skip f) g@(Fn 0 _) a (PushEnv bs b)
  = case g of -- for some reason, you can't give as much type annotations in the top level patternmatch
    ((Fn 0 g') :: Transform (x, Array sh e) (y, Array sh' e))
      | Just Refl <- eqT @sh @sh' -> case fuseEnvs f g' a bs of
        ValArr' tr valarr -> ValArr' (Fn 0 tr) (PushEnv valarr b)
    _ -> error "asdfasdfsdfg"
fuseEnvs (Fn 0 f) (Skip g) a b = undefined --TODO
fuseEnvs _ _ _ _ = error "fuseEnvs"

-- evaluate one iteration of a loopbody
evalLB :: LoopBody pinputs tinputs outputs x y
       -> ValArr pinputs
       -> ValArr tinputs'
       -> ValArr outputs'
       -> Transform tinputs tinputs'
       -> Transform outputs outputs'
       -> IO ()
evalLB Base _ _ _ Id Id = return ()
-- Evaluate the LoopBody' and recurse
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       Id       = evalLB' lb' 0 0 p t o >> evalLB lb p ts os Id Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) Id       = evalLB' lb' i 0 p t o >> evalLB lb p ts os a  Id
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) Id       (Fn j b) = evalLB' lb' 0 j p t o >> evalLB lb p ts os Id b
evalLB (Take lb' lb) p (PushEnv ts t) (PushEnv os o) (Fn i a) (Fn j b) = evalLB' lb' i j p t o >> evalLB lb p ts os a  b
-- TODO this one is not quite right
evalLB Use{} _ _ PushEnv{} _ _ = undefined --(Use xs r lb) p ts             (PushEnv os o) ti       Id        = readIORef r >>= \i -> modifyIORef r (+1) >> assignArr (-i) xs o >> evalLB lb p ts os ti Id
--evalLB Use{} _ _ _ _ _ = undefined --(Use xs r lb) p ts             (PushEnv os o) ti       (Fn j b)  = readIORef r >>= \i -> modifyIORef r (+1) >> assignArr (j-i)    xs o >> evalLB lb p ts os ti b
-- Recurse
evalLB lb p (PushEnv ts _) o (Skip idxt) idxo = evalLB lb p ts o idxt idxo
evalLB lb p t (PushEnv os _) idxt (Skip idxo) = evalLB lb p t os idxt idxo

                                              -- There is no Transform
evalLB Take{} _ EmptyEnv _ x _ = case x of {} -- possible for these cases,
evalLB Take{} _ _ EmptyEnv _ x = case x of {} -- so this satisfies GHC's
evalLB Use {} _ _ EmptyEnv _ x = case x of {} -- incomplete pattern check



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

