{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}-- making Neg1 an instance of these typeclasses is, in some cases, an ugly hack and not meaningful. You should never have an array element of type Neg1
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
module Data.Array.Accelerate.Trafo.NewFusion.Neg1 where

import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Type
import Data.Typeable




data Neg1 = Neg1 deriving (Show, Typeable)
instance ArrayElt Neg1 where
  type ArrayPtrs Neg1 = Neg1
instance Elt Neg1 where
  type EltRepr Neg1 = ()
  eltType       = TypeRunit
  fromElt Neg1   = ()
  toElt ()      = Neg1
class Elt a => Shapeish a where
  totalSize :: a -> Int
instance {-# INCOHERENT #-} {- OVERLAPPABLE -} (Elt a, Shape a) => Shapeish a where
  totalSize = size
instance {- OVERLAPPING -} Shapeish Neg1 where
  totalSize _ = 1


-- -- WHY
-- g :: (Shapeish a) => a -> a
-- g = id