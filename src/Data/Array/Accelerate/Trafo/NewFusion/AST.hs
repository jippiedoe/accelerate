{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}

{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module Data.Array.Accelerate.Trafo.NewFusion.AST (
  NodeId (..),
  PreLabelledAcc (..),
  LabelledOpenAcc (..),
  LabelledAcc,
  ArrayVars (..),
  GroupedLabelledAcc (..),
  PreFusedOpenAcc (..),
  Numerousness (..),
  FusedAcc,
  FusedAfun,
  FusedExp,
  FusedFun,
  FusedOpenAcc,
  FusedOpenAfun,
  FusedOpenExp,
  FusedOpenFun,
  LabelledOpenAfun,
  LabelledOpenExp,
  LabelledOpenFun
  ) where


import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Array.Representation     (SliceIndex(..))
import Data.Array.Accelerate.AST                      hiding ( PreOpenAcc(..), OpenAcc(..), Acc )
import qualified Data.Array.Accelerate.AST            as AST


newtype NodeId = NodeId Int deriving (Eq, Show, Ord)

type LabelledAcc = LabelledOpenAcc ()
newtype LabelledOpenAcc aenv a = LabelledOpenAcc (PreLabelledAcc LabelledOpenAcc aenv a)

data GroupedLabelledAcc aenv a where
  EverythingInsideThisIsOneGroup :: LabelledOpenAcc aenv a -> GroupedLabelledAcc aenv a
  ContainsMultipleGroups :: PreLabelledAcc GroupedLabelledAcc aenv a -> GroupedLabelledAcc aenv a



type FusedAcc  = FusedOpenAcc ()
type FusedAfun = FusedOpenAfun ()
type FusedExp  = FusedOpenExp ()
type FusedFun  = FusedOpenFun ()
type FusedOpenAcc  = PreFusedOpenAcc Multiple
type FusedOpenAfun = PreOpenAfun FusedOpenAcc
type FusedOpenExp  = PreOpenExp  FusedOpenAcc
type FusedOpenFun  = PreOpenFun  FusedOpenAcc

-- The extra parameter 'n' signifies whether the contained acc is fused into a single pass.
-- This guarantees that the fused tree is consistent with itself.
data Numerousness = Single | Multiple
data PreFusedOpenAcc (n :: Numerousness) aenv a where
  RootOfCluster :: PreFusedOpenAcc Single   aenv a
                -> PreFusedOpenAcc Multiple aenv a

  Unfused       :: AST.PreOpenAcc (PreFusedOpenAcc Multiple) aenv a
                -> PreFusedOpenAcc Multiple                  aenv a

  LeafOfCluster :: AST.OpenAcc            aenv a
                -> PreFusedOpenAcc Single aenv a

  Vertical      ::
    { lhsV      :: LeftHandSide a aenv benv
    , innerV    :: PreFusedOpenAcc Single aenv a
    , outerV    :: PreFusedOpenAcc Single benv b
    }           -> PreFusedOpenAcc Single aenv b

  Horizontal    ::
    { leftH     :: PreFusedOpenAcc Single aenv  a
    , rightH    :: PreFusedOpenAcc Single aenv    b
    }           -> PreFusedOpenAcc Single aenv (a,b)

  Diagonal      ::
    { lhsD      :: LeftHandSide a aenv benv
    , firstD    :: PreFusedOpenAcc Single aenv  a
    , secondD   :: PreFusedOpenAcc Single benv    b
    }           -> PreFusedOpenAcc Single aenv (a,b)



data PreLabelledAcc acc aenv a where
  Alet        :: LeftHandSide bndArrs aenv aenv'
              -> acc                  aenv  bndArrs   -- bound expression
              -> acc                  aenv' bodyArrs  -- the bound expression scope
              -> PreLabelledAcc   acc aenv  bodyArrs

  Variable    :: NodeId
              -> ArrayVars          aenv a
              -> PreLabelledAcc acc aenv a

  Apply       :: NodeId
              -> PreOpenAfun     acc aenv (arrs1 -> arrs2)
              -> ArrayVars           aenv  arrs1
              -> PreLabelledAcc  acc aenv           arrs2

  Aforeign    :: (Arrays as, Arrays bs, Foreign asm)
              => NodeId
              -> asm                       (as -> bs)                 -- The foreign function for a given backend
              -> PreAfun          acc      (ArrRepr as -> ArrRepr bs) -- Fallback implementation(s)
              -> ArrayVars            aenv (ArrRepr as)               -- Arguments to the function
              -> PreLabelledAcc   acc aenv (ArrRepr bs)

  Acond       :: NodeId
              -> PreExp         acc aenv Bool
              -> acc                aenv arrs
              -> acc                aenv arrs
              -> PreLabelledAcc acc aenv arrs

  Awhile      :: NodeId
              -> PreOpenAfun     acc aenv (arrs -> Scalar Bool)     -- continue iteration while true
              -> PreOpenAfun     acc aenv (arrs -> arrs)            -- function to iterate
              -> ArrayVars           aenv  arrs                     -- initial value
              -> PreLabelledAcc  acc aenv  arrs

  Use         :: (Shape sh, Elt e)
              => NodeId
              -> Array sh e
              -> PreLabelledAcc acc aenv (Array sh e)

  Unit        :: Elt e
              => NodeId
              -> PreExp         acc aenv e
              -> PreLabelledAcc acc aenv (Scalar e)

  Reshape     :: (Shape sh, Shape sh', Elt e)
              => NodeId
              -> PreExp         acc aenv sh                         -- new shape
              -> ArrayVars          aenv (Array sh' e)              -- array to be reshaped
              -> PreLabelledAcc acc aenv (Array sh  e)

  Generate    :: (Shape sh, Elt e)
              => NodeId
              -> PreExp         acc aenv sh                         -- output shape
              -> PreFun         acc aenv (sh -> e)                  -- representation function
              -> PreLabelledAcc acc aenv (Array sh e)

  Transform   :: (Elt a, Elt b, Shape sh, Shape sh')
              => NodeId
              -> PreExp         acc aenv sh'                        -- dimension of the result
              -> PreFun         acc aenv (sh' -> sh)                -- index permutation function
              -> PreFun         acc aenv (a   -> b)                 -- function to apply at each element
              -> ArrayVars          aenv (Array sh  a)              -- source array
              -> PreLabelledAcc acc aenv (Array sh' b)

  Replicate   :: (Shape sh, Shape sl, Elt slix, Elt e)
              => NodeId
              -> SliceIndex (EltRepr slix)                      -- slice type specification
                            (EltRepr sl)
                            co
                            (EltRepr sh)
              -> PreExp         acc aenv slix                       -- slice value specification
              -> ArrayVars          aenv (Array sl e)               -- data to be replicated
              -> PreLabelledAcc acc aenv (Array sh e)

  Slice       :: (Shape sh, Shape sl, Elt slix, Elt e)
              => NodeId
              -> SliceIndex (EltRepr slix)                      -- slice type specification
                            (EltRepr sl)
                            co
                            (EltRepr sh)
              -> ArrayVars          aenv (Array sh e)               -- array to be indexed
              -> PreExp         acc aenv slix                       -- slice value specification
              -> PreLabelledAcc acc aenv (Array sl e)

  Map         :: (Shape sh, Elt e, Elt e')
              => NodeId
              -> PreFun         acc aenv (e -> e')
              -> ArrayVars          aenv (Array sh e)
              -> PreLabelledAcc acc aenv (Array sh e')

  ZipWith     :: (Shape sh, Elt e1, Elt e2, Elt e3)
              => NodeId
              -> PreFun         acc aenv (e1 -> e2 -> e3)
              -> ArrayVars          aenv (Array sh e1)
              -> ArrayVars          aenv (Array sh e2)
              -> PreLabelledAcc acc aenv (Array sh e3)

  Fold        :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- default value
              -> ArrayVars          aenv (Array (sh:.Int) e)        -- folded array
              -> PreLabelledAcc acc aenv (Array sh e)

  Fold1       :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVars          aenv (Array (sh:.Int) e)        -- folded array
              -> PreLabelledAcc acc aenv (Array sh e)

  FoldSeg     :: (Shape sh, Elt e, Elt i, IsIntegral i)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- default value
              -> ArrayVars          aenv (Array (sh:.Int) e)        -- folded array
              -> ArrayVars          aenv (Segments i)               -- segment descriptor
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Fold1Seg    :: (Shape sh, Elt e, Elt i, IsIntegral i)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVars          aenv (Array (sh:.Int) e)        -- folded array
              -> ArrayVars          aenv (Segments i)               -- segment descriptor
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Scanl       :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Scanl'      :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (ArrRepr (Array (sh:.Int) e, Array sh e))

  Scanl1      :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Scanr       :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Scanr'      :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (ArrRepr (Array (sh:.Int) e, Array sh e))

  Scanr1      :: (Shape sh, Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVars          aenv (Array (sh:.Int) e)
              -> PreLabelledAcc acc aenv (Array (sh:.Int) e)

  Permute     :: (Shape sh, Shape sh', Elt e)
              => NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVars          aenv (Array sh' e)              -- default values
              -> PreFun         acc aenv (sh -> sh')                -- permutation function
              -> ArrayVars          aenv (Array sh e)               -- source array
              -> PreLabelledAcc acc aenv (Array sh' e)

  Backpermute :: (Shape sh, Shape sh', Elt e)
              => NodeId
              -> PreExp         acc aenv sh'                        -- dimensions of the result
              -> PreFun         acc aenv (sh' -> sh)                -- permutation function
              -> ArrayVars          aenv (Array sh e)               -- source array
              -> PreLabelledAcc acc aenv (Array sh' e)

  Stencil     :: (Elt e, Elt e', Stencil sh e stencil)
              => NodeId
              -> PreFun          acc aenv (stencil -> e')           -- stencil function
              -> PreBoundary     acc aenv (Array sh e)              -- boundary condition
              -> ArrayVars           aenv (Array sh e)              -- source array
              -> PreLabelledAcc  acc aenv (Array sh e')

  Stencil2    :: (Elt a, Elt b, Elt c, Stencil sh a stencil1, Stencil sh b stencil2)
              => NodeId
              -> PreFun         acc aenv (stencil1 -> stencil2 -> c) -- stencil function
              -> PreBoundary    acc aenv (Array sh a)                -- boundary condition #1
              -> ArrayVars          aenv (Array sh a)                -- source array #1
              -> PreBoundary    acc aenv (Array sh b)                -- boundary condition #2
              -> ArrayVars          aenv (Array sh b)                -- source array #2
              -> PreLabelledAcc acc aenv (Array sh c)

-- used to bind variables in PreLabelledAcc

type LabelledOpenExp  = PreOpenExp  LabelledOpenAcc
type LabelledOpenFun  = PreOpenFun  LabelledOpenAcc
type LabelledOpenAfun = PreOpenAfun LabelledOpenAcc



instance HasArraysRepr LabelledOpenAcc where
  arraysRepr (LabelledOpenAcc a) = arraysRepr a

instance HasArraysRepr acc => HasArraysRepr (PreLabelledAcc acc) where
  arraysRepr (Alet _ _ body)                      = arraysRepr body
  arraysRepr (Variable _ x)                         = arraysRepr x
  arraysRepr (Apply _ (Alam _ (Abody a)) _)       = arraysRepr a
  arraysRepr Apply{}                              = error "Tomorrow will arrive, on time"
  arraysRepr (Aforeign _ _ (Alam _ (Abody a)) _)  = arraysRepr a
  arraysRepr (Aforeign _ _ (Abody _) _)           = error "And what have you got, at the end of the day?"
  arraysRepr (Aforeign _ _ (Alam _ (Alam _ _)) _) = error "A bottle of whisky. And a new set of lies."
  arraysRepr (Acond _ _ whenTrue _)               = arraysRepr whenTrue
  arraysRepr (Awhile _ _ (Alam lhs _) _)          = lhsToArraysR lhs
  arraysRepr Awhile{}                             = error "I want my, I want my MTV!"
  arraysRepr Use{}                                = ArraysRarray
  arraysRepr Unit{}                               = ArraysRarray
  arraysRepr Reshape{}                            = ArraysRarray
  arraysRepr Generate{}                           = ArraysRarray
  arraysRepr Transform{}                          = ArraysRarray
  arraysRepr Replicate{}                          = ArraysRarray
  arraysRepr Slice{}                              = ArraysRarray
  arraysRepr Map{}                                = ArraysRarray
  arraysRepr ZipWith{}                            = ArraysRarray
  arraysRepr Fold{}                               = ArraysRarray
  arraysRepr Fold1{}                              = ArraysRarray
  arraysRepr FoldSeg{}                            = ArraysRarray
  arraysRepr Fold1Seg{}                           = ArraysRarray
  arraysRepr Scanl{}                              = ArraysRarray
  arraysRepr Scanl'{}                             = arraysRtuple2
  arraysRepr Scanl1{}                             = ArraysRarray
  arraysRepr Scanr{}                              = ArraysRarray
  arraysRepr Scanr'{}                             = arraysRtuple2
  arraysRepr Scanr1{}                             = ArraysRarray
  arraysRepr Permute{}                            = ArraysRarray
  arraysRepr Backpermute{}                        = ArraysRarray
  arraysRepr Stencil{}                            = ArraysRarray
  arraysRepr Stencil2{}                           = ArraysRarray
