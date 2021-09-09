{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Representation.Ground
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Representation.Ground
  where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Type.Equality

-- | Ground values are buffers or scalars.
--
data GroundR a where
  GroundRbuffer :: ScalarType e -> GroundR (Buffer e)
  GroundRscalar :: ScalarType e -> GroundR e

-- | Tuples of ground values
--
type GroundsR = TupR GroundR

rnfGroundR :: GroundR t -> ()
rnfGroundR (GroundRscalar tp) = rnfScalarType tp
rnfGroundR (GroundRbuffer tp) = rnfScalarType tp

rnfGroundsR :: GroundsR t -> ()
rnfGroundsR = rnfTupR rnfGroundR

-- | Conversion from arrays representation to grounds representation
desugarArraysR :: ArraysR arr -> GroundsR (DesugaredArrays arr)
desugarArraysR TupRunit          = TupRunit
desugarArraysR (TupRsingle repr) = desugarArrayR repr
desugarArraysR (TupRpair r1 r2)  = desugarArraysR r1 `TupRpair` desugarArraysR r2

desugarArrayR :: ArrayR arr -> GroundsR (DesugaredArrays arr)
desugarArrayR (ArrayR shr tp) = mapTupR GroundRscalar (shapeType shr) `TupRpair` buffersR tp

buffersR :: forall e. TypeR e -> GroundsR (Buffers e)
buffersR TupRunit           = TupRunit
buffersR (TupRsingle tp)
  | Refl <- reprIsSingle @ScalarType @e @Buffer tp = TupRsingle (GroundRbuffer tp)
buffersR (TupRpair t1 t2)   = buffersR t1 `TupRpair` buffersR t2

type family DesugaredArrays a where
  DesugaredArrays ()           = ()
  DesugaredArrays (a, b)       = (DesugaredArrays a, DesugaredArrays b)
  DesugaredArrays (Array sh e) = (sh, Buffers e)

type family DesugaredAfun a where
  DesugaredAfun (a -> b) = DesugaredArrays a -> DesugaredAfun b
  DesugaredAfun a        = DesugaredArrays a

desugaredAfunIsBody :: ArraysR a -> DesugaredAfun a :~: DesugaredArrays a
desugaredAfunIsBody (TupRsingle ArrayR{}) = Refl
desugaredAfunIsBody TupRunit              = Refl
desugaredAfunIsBody (TupRpair _ _)        = Refl

desugarArrays :: ArraysR a -> a -> DesugaredArrays a
desugarArrays TupRunit              ()                 = ()
desugarArrays (TupRpair r1 r2)      (a1, a2)           = (desugarArrays r1 a1, desugarArrays r2 a2)
desugarArrays (TupRsingle ArrayR{}) (Array sh buffers) = (sh, buffers)

sugarArrays :: ArraysR a -> DesugaredArrays a -> a
sugarArrays TupRunit              ()            = ()
sugarArrays (TupRpair r1 r2)      (d1, d2)      = (sugarArrays r1 d1, sugarArrays r2 d2)
sugarArrays (TupRsingle ArrayR{}) (sh, buffers) = Array sh buffers