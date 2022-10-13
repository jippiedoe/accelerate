{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp (LimpProvider) where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP, Var, BackendVar)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver

import qualified Numeric.Limp.Canon as L
import qualified Numeric.Limp.Rep as L (IntDouble, Assignment(..), Z(..), R(..))
import qualified Numeric.Limp.Solve.Simplex.StandardForm as L (standard)
import qualified Numeric.Limp.Solve.Simplex.Maps as L (simplex, assignment)
import qualified Numeric.Limp.Solve.Branch.Simple as L (branch)

import Data.Bifunctor (bimap)
import Data.List (inits, tails)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Proxy (Proxy)
import qualified Data.Set as Set
import Data.Void (Void)


data LimpProvider

instance MakesILP op => ILPSolver LimpProvider () op where
  solve :: Proxy LimpProvider -> s -> ILP op -> IO (Maybe (Solution op))
  solve _ _ ilp = return $
    let SaneILP dir obj preConstrs = eliminateEqualities (toSane ilp)
        (objExpr, _objConst) = exprToLimp obj
        (constrs, bounds) = splitOutBounds preConstrs
        objMultiplier = case dir of Maximise -> -1
                                    Minimise -> 1
        definfbounds = Map.fromList [(Left v, (Nothing, Nothing))
                                    | v <- Set.toList $ allvars obj <> allvarsC preConstrs]
        program = L.Program
          { L._objective = case objExpr of L.Linear m -> L.Linear ((* objMultiplier) <$> m)
          , L._constraints = L.Constraint (map constraintToLimp constrs)
          , L._bounds = boundsToLimp bounds <> definfbounds   -- note: left-biased union
          }
    in unlimpify . fst <$> L.branch (fmap L.assignment . L.simplex . L.standard) program
    where
      allvars (Expr terms _) = Map.keysSet terms
      allvarsC l = foldMap (\(e1, _, e2) -> allvars e1 <> allvars e2) l

data SaneILP op = SaneILP OptDir (Expr op) [(Expr op, Rel, Expr op)]
data Expr op = Expr (Map (Var op) Int) Int
data Rel = RLE | REQ | RGE

instance Ord (BackendVar op) => Semigroup (Expr op) where
  Expr m1 c1 <> Expr m2 c2 = Expr (Map.unionWith (+) m1 m2) (c1 + c2)
instance Ord (BackendVar op) => Monoid (Expr op) where
  mempty = Expr mempty 0

negExpr :: Expr op -> Expr op
negExpr (Expr terms cnst) = Expr (negate <$> terms) (-cnst)

toSane :: Ord (BackendVar op) => ILP op -> SaneILP op
toSane (ILP dir target constrs bnds n) =
  SaneILP dir (saneExpr target) (saneConstrs constrs ++ saneBounds bnds)
  where
    saneExpr :: Ord (BackendVar op) => Expression op -> Expr op
    saneExpr (Constant (Number f)) = Expr mempty (f n)
    saneExpr (e1 :+ e2) = saneExpr e1 <> saneExpr e2
    saneExpr (Number f :* var) = Expr (Map.singleton var (f n)) 0

    saneConstrs :: Ord (BackendVar op) => Constraint op -> [(Expr op, Rel, Expr op)]
    saneConstrs (e1 :<= e2) = pure (saneExpr e1, RLE, saneExpr e2)
    saneConstrs (e1 :>= e2) = pure (saneExpr e1, RGE, saneExpr e2)
    saneConstrs (e1 :== e2) = pure (saneExpr e1, REQ, saneExpr e2)
    saneConstrs (c1 :&& c2) = saneConstrs c1 <> saneConstrs c2
    saneConstrs TrueConstraint = mempty

    saneBounds :: Ord (BackendVar op) => Bounds op -> [(Expr op, Rel, Expr op)]
    saneBounds (Binary v) = saneBounds (Lower 0 v) <> saneBounds (Upper v 1)
    saneBounds (LowerUpper a v b) = saneBounds (Lower a v) <> saneBounds (Upper v b)
    saneBounds (Lower a v) = pure (Expr mempty (fromIntegral a), RLE, Expr (Map.singleton v 1) 0)
    saneBounds (Upper v b) = pure (Expr (Map.singleton v 1) 0, RLE, Expr mempty (fromIntegral b))
    saneBounds (a :<> b) = saneBounds a <> saneBounds b
    saneBounds NoBounds = mempty

exprToLimp :: Ord (BackendVar op) => Expr op -> (L.Linear (Var op) Void L.IntDouble, Int)
exprToLimp (Expr terms cnst) = (exprToLimp' terms, cnst)

exprToLimp' :: Ord (BackendVar op) => Map (Var op) Int -> L.Linear (Var op) Void L.IntDouble
exprToLimp' terms = L.Linear (Map.mapKeys Left (fromIntegral <$> terms))

constraintToLimp :: Ord (BackendVar op) => (Expr op, Rel, Expr op) -> L.Constraint1 (Var op) Void L.IntDouble
constraintToLimp (e1, RLE, e2) =
  -- (Expr terms 0) <= -cnst
  let Expr terms cnst = e1 <> negExpr e2
  in L.C1 Nothing (exprToLimp' terms) (Just (L.R (fromIntegral (-cnst))))
constraintToLimp (e1, RGE, e2) = constraintToLimp (e2, RLE, e1)
constraintToLimp (_, REQ, _) = error "Equalities should be gone by now"

boundsToLimp :: Ord (BackendVar op)
             => Map (Var op) (Maybe Int, Maybe Int)
             -> Map (Either (Var op) Void) (Maybe (L.R L.IntDouble), Maybe (L.R L.IntDouble))
boundsToLimp = Map.mapKeys Left . fmap (bimap (fmap fromIntegral) (fmap fromIntegral))

splitOutBounds :: Ord (BackendVar op)
               => [(Expr op, Rel, Expr op)]
               -> ([(Expr op, Rel, Expr op)], Map (Var op) (Maybe Int, Maybe Int))
splitOutBounds =
  foldr (bimap2 (++)
                (Map.unionWith (bimap2 (combine max) (combine min))) . discriminate)
        ([], mempty)
  where
    combine :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
    combine _ Nothing x = x
    combine _ x Nothing = x
    combine g (Just x) (Just y) = Just (g x y)

    discriminate :: Ord (BackendVar op)
                 => (Expr op, Rel, Expr op)
                 -> ([(Expr op, Rel, Expr op)], Map (Var op) (Maybe Int, Maybe Int))
    discriminate (lhs, RGE, rhs) = discriminate (rhs, RLE, lhs)
    discriminate (lhs, RLE, rhs) =
      -- (Expr terms cnst) <= 0
      -- (Expr terms 0) <= rhs'
      let Expr terms cnst = lhs <> negExpr rhs
          rhs' = -cnst
      in case Map.assocs terms of
           [(var, coef)] ->
             -- coef * var <= rhs'
             case compare coef 0 of
               LT ->
                 -- -coef * var >= -rhs'   and -coef > 0
                 -- var >= -rhs' / -coef
                 ([], Map.singleton var (Just ((-rhs') `ceilDiv` (-coef)), Nothing))
                 where ceilDiv a b = (a + b - 1) `div` b  -- requires b > 0
               EQ ->
                 -- 0 * var <= rhs'
                 if rhs' >= 0 then ([], mempty)
                              else error "limp convert: Unsatisfiable absurd inequality"
               GT ->
                 -- coef * var <= rhs'   and coef > 0
                 -- var <= rhs' / coef
                 ([], Map.singleton var (Nothing, Just (rhs' `div` coef)))
           _ ->
             -- if it's not a single term, just preserve it as a constraint
             ([(lhs, RLE, rhs)], mempty)
    discriminate (_, REQ, _) = error "Equalities should be gone by now"

data Equality op = TrivialEquality | Equality (Var op) (Expr op)

solveEquality :: Ord (BackendVar op) => Expr op -> Expr op -> Equality op
solveEquality e1 e2 =
  -- e1 = e2  <=>  e = e1 - e2 = 0
  let Expr terms cnst = e1 <> negExpr e2
  in if | Map.null terms
        -> if cnst == 0 then TrivialEquality
                        else error "limp convert: Unsatisfiable absurd equality"
        | let terms' = Map.assocs terms
        , (pre, (var, coef), post) : _ <- [x | x@(_, (_, coef), _) <- splits terms'
                                             , abs coef == 1]
        , let restexpr = Expr (Map.fromList (pre ++ post)) cnst
        -> Equality var
                    (if coef == 1 then negExpr restexpr else restexpr)
        | otherwise
        -> error "limp convert: Unsupported equality with no 1-coefficient variables"

substitute :: Ord (BackendVar op) => Equality op -> SaneILP op -> SaneILP op
substitute equ (SaneILP dir target constrs) =
  SaneILP dir (subL equ target)
              (map (\(lhs, rel, rhs) -> (subL equ lhs, rel, subL equ rhs)) constrs)
  where
    subL TrivialEquality e = e
    subL (Equality var def) (Expr terms cnst) =
      let subTerm (v, coef)
            | v == var = def
            | otherwise = Expr (Map.singleton v coef) 0
      in foldMap subTerm (Map.assocs terms) <> Expr mempty cnst

eliminateEqualities :: Ord (BackendVar op) => SaneILP op -> SaneILP op
eliminateEqualities ilp@(SaneILP dir target constrs) =
  case [x | x@(_, (_, REQ, _), _) <- splits constrs] of
    [] -> ilp
    (pre, (lhs, _, rhs), post) : _ ->
      let equ = solveEquality lhs rhs
      in eliminateEqualities (substitute equ (SaneILP dir target (pre ++ post)))

unlimpify :: L.Assignment (Var op) Void L.IntDouble -> Solution op
unlimpify (L.Assignment zvarmap rvarmap)
  | Map.null rvarmap = Map.map (\(L.Z x) -> x) zvarmap
  | otherwise = error "Real variables found in Limp ILP solution"

bimap2 :: (a -> b -> c) -> (d -> e -> f) -> (a, d) -> (b, e) -> (c, f)
bimap2 f g (x, y) (x', y') = (f x x', g y y')

splits :: [a] -> [([a], a, [a])]
splits l = zip3 (inits l) l (tail (tails l))
