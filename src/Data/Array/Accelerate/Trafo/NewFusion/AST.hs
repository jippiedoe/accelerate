{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}

{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module Data.Array.Accelerate.Trafo.NewFusion.AST
  ( NodeId(..)
  , PreLabelledAcc(..)
  , LabelledOpenAcc(..)
  , LabelledAcc
  , ArrayVars(..)
  , GroupedLabelledAcc(..)
  , PreFusedOpenAcc(..)
  , Numerousness(..)
  , FusedAcc
  , FusedAfun
  , FusedExp
  , FusedFun
  , FusedOpenAcc
  , FusedOpenAfun
  , FusedOpenExp
  , FusedOpenFun
  , LabelledOpenAfun
  , LabelledOpenExp
  , LabelledOpenFun
  )
where


import           Data.Array.Accelerate.Type
import           qualified Data.Array.Accelerate.Array.Sugar as Sugar
import           Data.Array.Accelerate.Array.Representation
import           Data.Array.Accelerate.AST
                                         hiding ( PreOpenAcc(..)
                                                , OpenAcc(..)
                                                , Acc
                                                )
import qualified Data.Array.Accelerate.AST     as AST


newtype NodeId = NodeId Int deriving (Eq, Show, Ord)

type LabelledAcc = LabelledOpenAcc ()
newtype LabelledOpenAcc aenv a = LabelledOpenAcc (PreLabelledAcc LabelledOpenAcc aenv a)

data GroupedLabelledAcc aenv a where
  EverythingInsideThisIsOneGroup ::LabelledOpenAcc aenv a -> GroupedLabelledAcc aenv a
  ContainsMultipleGroups ::PreLabelledAcc GroupedLabelledAcc aenv a -> GroupedLabelledAcc aenv a



type FusedAcc = FusedOpenAcc ()
type FusedAfun = FusedOpenAfun ()
type FusedExp = FusedOpenExp ()
type FusedFun = FusedOpenFun ()
type FusedOpenAcc = PreFusedOpenAcc Multiple
type FusedOpenAfun = PreOpenAfun FusedOpenAcc
type FusedOpenExp = PreOpenExp FusedOpenAcc
type FusedOpenFun = PreOpenFun FusedOpenAcc

-- The extra parameter 'n' signifies whether the contained acc is fused into a single pass.

-- This guarantees that the fused tree is consistent with itself.

data Numerousness = Single | Multiple
data PreFusedOpenAcc (n :: Numerousness) aenv a where
  RootOfFusionTree ::PreFusedOpenAcc Single   aenv a
                   -> PreFusedOpenAcc Multiple aenv a

  Unfused          ::AST.PreOpenAcc (PreFusedOpenAcc Multiple) aenv a
                   -> PreFusedOpenAcc Multiple                  aenv a

  LeafOfFusionTree ::AST.OpenAcc            aenv a
                   -> PreFusedOpenAcc Single aenv a

  Vertical         ::{ lhsV         :: ALeftHandSide a aenv benv
    , innerV       :: PreFusedOpenAcc Single aenv a
    , outerV       :: PreFusedOpenAcc Single benv b
    }              -> PreFusedOpenAcc Single aenv b

  Horizontal       ::{ leftH        :: PreFusedOpenAcc Single aenv  a
    , rightH       :: PreFusedOpenAcc Single aenv    b
    }              -> PreFusedOpenAcc Single aenv (a,b)

  Diagonal         ::{ lhsD         :: ALeftHandSide a aenv benv
    , firstD       :: PreFusedOpenAcc Single aenv  a
    , secondD      :: PreFusedOpenAcc Single benv    b
    }              -> PreFusedOpenAcc Single aenv (a,b)



data PreLabelledAcc acc aenv a where
  Alet        ::ALeftHandSide bndArrs aenv aenv'
              -> acc                  aenv  bndArrs   -- bound expression
              -> acc                  aenv' bodyArrs  -- the bound expression scope
              -> PreLabelledAcc   acc aenv  bodyArrs

  Variable    ::NodeId
              -> ArrayVars          aenv a
              -> PreLabelledAcc acc aenv a

  Apply       ::NodeId
              -> ArraysR arrs2
              -> PreOpenAfun     acc aenv (arrs1 -> arrs2)
              -> ArrayVars           aenv  arrs1
              -> PreLabelledAcc  acc aenv           arrs2

  Aforeign    ::(Sugar.Arrays as, Sugar.Arrays bs, Sugar.Foreign asm)
              => NodeId
              -> asm                       (as -> bs)                 -- The foreign function for a given backend
              -> PreAfun          acc      (Sugar.ArrRepr as -> Sugar.ArrRepr bs) -- Fallback implementation(s)
              -> ArrayVars            aenv (Sugar.ArrRepr as)               -- Arguments to the function
              -> PreLabelledAcc   acc aenv (Sugar.ArrRepr bs)

  Acond       ::NodeId
              -> PreExp         acc aenv Bool
              -> acc                aenv arrs
              -> acc                aenv arrs
              -> PreLabelledAcc acc aenv arrs

  Awhile      ::NodeId
              -> PreOpenAfun     acc aenv (arrs -> Scalar Bool)     -- continue iteration while true
              -> PreOpenAfun     acc aenv (arrs -> arrs)            -- function to iterate
              -> ArrayVars           aenv  arrs                     -- initial value
              -> PreLabelledAcc  acc aenv  arrs

  Use         ::NodeId
              -> ArrayR (Array sh e)
              -> Array sh e
              -> PreLabelledAcc acc aenv (Array sh e)

  Unit        ::NodeId
              -> TupleType e
              -> PreExp         acc aenv e
              -> PreLabelledAcc acc aenv (Scalar e)

  Reshape     ::NodeId
              -> ShapeR sh
              -> PreExp         acc aenv sh                         -- new shape
              -> ArrayVar           aenv (Array sh' e)              -- array to be reshaped
              -> PreLabelledAcc acc aenv (Array sh  e)

  Generate    ::NodeId
              -> ArrayR (Array sh e)
              -> PreExp         acc aenv sh                         -- output shape
              -> PreFun         acc aenv (sh -> e)                  -- representation function
              -> PreLabelledAcc acc aenv (Array sh e)

  Transform   ::NodeId
              -> ArrayR (Array sh' b)
              -> PreExp         acc aenv sh'                        -- dimension of the result
              -> PreFun         acc aenv (sh' -> sh)                -- index permutation function
              -> PreFun         acc aenv (a   -> b)                 -- function to apply at each element
              -> ArrayVar           aenv (Array sh  a)              -- source array
              -> PreLabelledAcc acc aenv (Array sh' b)

  Replicate   ::NodeId
              -> SliceIndex slix                                -- slice type specification
                            sl
                            co
                            sh
              -> PreExp         acc aenv slix                       -- slice value specification
              -> ArrayVar           aenv (Array sl e)               -- data to be replicated
              -> PreLabelledAcc acc aenv (Array sh e)

  Slice       ::NodeId
              -> SliceIndex slix                      -- slice type specification
                            sl
                            co
                            sh
              -> ArrayVar           aenv (Array sh e)               -- array to be indexed
              -> PreExp         acc aenv slix                       -- slice value specification
              -> PreLabelledAcc acc aenv (Array sl e)

  Map         ::NodeId
              -> TupleType e'
              -> PreFun         acc aenv (e -> e')
              -> ArrayVar           aenv (Array sh e)
              -> PreLabelledAcc acc aenv (Array sh e')

  ZipWith     ::NodeId
              -> TupleType e3
              -> PreFun         acc aenv (e1 -> e2 -> e3)
              -> ArrayVar           aenv (Array sh e1)
              -> ArrayVar           aenv (Array sh e2)
              -> PreLabelledAcc acc aenv (Array sh e3)

  Fold        ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- default value
              -> ArrayVar           aenv (Array (sh, Int) e)        -- folded array
              -> PreLabelledAcc acc aenv (Array sh e)

  Fold1       ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVar           aenv (Array (sh, Int) e)        -- folded array
              -> PreLabelledAcc acc aenv (Array sh e)

  FoldSeg     ::NodeId
              -> IntegralType i
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- default value
              -> ArrayVar           aenv (Array (sh, Int) e)        -- folded array
              -> ArrayVar           aenv (Segments i)               -- segment descriptor
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Fold1Seg    ::NodeId
              -> IntegralType i
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVar           aenv (Array (sh, Int) e)        -- folded array
              -> ArrayVar           aenv (Segments i)               -- segment descriptor
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Scanl       ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Scanl'      ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e, Array sh e)

  Scanl1      ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Scanr       ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Scanr'      ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> PreExp         acc aenv e                          -- initial value
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e, Array sh e)

  Scanr1      :: NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVar           aenv (Array (sh, Int) e)
              -> PreLabelledAcc acc aenv (Array (sh, Int) e)

  Permute     ::NodeId
              -> PreFun         acc aenv (e -> e -> e)              -- combination function
              -> ArrayVar           aenv (Array sh' e)              -- default values
              -> PreFun         acc aenv (sh -> sh')                -- permutation function
              -> ArrayVar           aenv (Array sh e)               -- source array
              -> PreLabelledAcc acc aenv (Array sh' e)

  Backpermute ::NodeId
              -> ShapeR sh'
              -> PreExp         acc aenv sh'                        -- dimensions of the result
              -> PreFun         acc aenv (sh' -> sh)                -- permutation function
              -> ArrayVar           aenv (Array sh e)               -- source array
              -> PreLabelledAcc acc aenv (Array sh' e)

  Stencil     ::NodeId
              -> StencilR sh e stencil
              -> TupleType e'
              -> PreFun          acc aenv (stencil -> e')           -- stencil function
              -> PreBoundary     acc aenv (Array sh e)              -- boundary condition
              -> ArrayVar            aenv (Array sh e)              -- source array
              -> PreLabelledAcc  acc aenv (Array sh e')

  Stencil2    ::NodeId
              -> StencilR sh a stencil1
              -> StencilR sh b stencil2
              -> TupleType c
              -> PreFun         acc aenv (stencil1 -> stencil2 -> c) -- stencil function
              -> PreBoundary    acc aenv (Array sh a)                -- boundary condition #1
              -> ArrayVar           aenv (Array sh a)                -- source array #1
              -> PreBoundary    acc aenv (Array sh b)                -- boundary condition #2
              -> ArrayVar           aenv (Array sh b)                -- source array #2
              -> PreLabelledAcc acc aenv (Array sh c)

-- used to bind variables in PreLabelledAcc


type LabelledOpenExp = PreOpenExp LabelledOpenAcc
type LabelledOpenFun = PreOpenFun LabelledOpenAcc
type LabelledOpenAfun = PreOpenAfun LabelledOpenAcc



instance HasArraysRepr LabelledOpenAcc where
  arraysRepr (LabelledOpenAcc a) = arraysRepr a

instance HasArraysRepr acc => HasArraysRepr (PreLabelledAcc acc) where
  arraysRepr (Alet _ _ body                       ) = arraysRepr body
  arraysRepr (Variable _ x                        ) = arraysRepr x
  arraysRepr (Apply    _ repr _                  _) = repr
  arraysRepr (Aforeign _ _    (Alam _ (Abody a)) _) = arraysRepr a
  arraysRepr (Aforeign _ _ (Abody _) _)             = error "And what have you got, at the end of the day?"
  arraysRepr (Aforeign _ _ (Alam _ (Alam _ _)) _)   = error "A bottle of whisky. And a new set of lies."
  arraysRepr (Acond  _ _ whenTrue     _)   = arraysRepr whenTrue
  arraysRepr (Awhile _ _ (Alam lhs _) _)   = lhsToTupR lhs
  arraysRepr Awhile{}                      = error "I want my, I want my MTV!"
  arraysRepr (Use  _ repr _              ) =TupRsingle repr
  arraysRepr (Unit _ tp   _              ) =arraysRarray ShapeRz tp
  arraysRepr (Reshape  _ sh   _ a        ) =let ArrayR _ tp = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (Generate _ repr _ _        ) =TupRsingle repr
  arraysRepr (Transform _ repr _ _ _ _   ) =TupRsingle repr
  arraysRepr (Replicate _ slice _ a      ) =let ArrayR _ tp = arrayRepr a
                                                  in  arraysRarray (sliceDomainR slice) tp
  arraysRepr (Slice     _ slice a _      ) =let ArrayR _ tp = arrayRepr a
                                                  in  arraysRarray (sliceShapeR slice) tp
  arraysRepr (Map       _ tp    _ a      ) =let ArrayR sh _ = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (ZipWith _ tp _ a _         ) =let ArrayR sh _ = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (Fold _ _ _ a               ) =let ArrayR (ShapeRsnoc sh) tp = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (Fold1 _ _ a                ) =let ArrayR (ShapeRsnoc sh) tp = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (FoldSeg _ _ _ _ a _        ) =arraysRepr a
  arraysRepr (Fold1Seg _ _ _ a _         ) =arraysRepr a
  arraysRepr (Scanl  _ _ _ a             ) =arraysRepr a
  arraysRepr (Scanl' _ _ _ a             ) =let repr@(ArrayR (ShapeRsnoc sh) tp) = arrayRepr a
                                                  in  TupRsingle repr `TupRpair` TupRsingle (ArrayR sh tp)
  arraysRepr (Scanl1 _ _ a               ) =arraysRepr a
  arraysRepr (Scanr  _ _ _ a             ) =arraysRepr a
  arraysRepr (Scanr' _ _ _ a             ) =let repr@(ArrayR (ShapeRsnoc sh) tp) = arrayRepr a
                                                  in  TupRsingle repr `TupRpair` TupRsingle (ArrayR sh tp)
  arraysRepr (Scanr1 _ _ a               ) =arraysRepr a
  arraysRepr (Permute     _ _  a _ _     ) =arraysRepr a
  arraysRepr (Backpermute _ sh _ _ a     ) =let ArrayR _ tp = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (Stencil _ _ tp _ _ a       ) =let ArrayR sh _ = arrayRepr a
                                                  in  arraysRarray sh tp
  arraysRepr (Stencil2 _ _ _ tp _ _ a _ _) =let ArrayR sh _ = arrayRepr a
                                                  in  arraysRarray sh tp
