{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}


-- This module implements a version of Category that can be constrained, like in the packages constrained-category and subhask.
module Data.Array.Accelerate.Trafo.NewFusion.Category where
import GHC.Exts (Constraint)

class Category k where
  type Object k o :: Constraint
  type Object k o = ()
  id :: Object k a => k a a
  (.) :: (Object k a, Object k b, Object k c)
         => k b c -> k a b -> k a c



instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)