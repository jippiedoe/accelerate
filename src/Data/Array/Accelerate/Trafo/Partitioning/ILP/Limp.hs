{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP, Var, BackendVar)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver

import qualified Numeric.Limp.Canon as L
import qualified Numeric.Limp.Rep as L (IntDouble, Assignment(..), Z(..), R(..))
import qualified Numeric.Limp.Solve.Simplex.StandardForm as L (standard)
import qualified Numeric.Limp.Solve.Simplex.Maps as L (simplex, assignment)
import qualified Numeric.Limp.Solve.Branch.Simple as L (branch)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Proxy (Proxy)
import Data.Void (Void)
import Data.Bifunctor (bimap)
import Data.Either (lefts)


data LimpProvider

instance MakesILP op => ILPSolver LimpProvider () op where
  solve :: Proxy LimpProvider -> s -> ILP op -> IO (Maybe (Solution op))
  solve _ _ (ILP dir obj constr bnds n) = return $
    let (objExpr, _objConst) = exprToLinear n obj
        constr' = L.Constraint (normaliseConstr n constr)
        objMultiplier = case dir of Maximise -> -1
                                    Minimise -> 1
        definfbounds = Map.fromList [(Left v, (Nothing, Nothing))
                                    | v <- allvars objExpr ++ allvarsC constr']
        program = L.Program
          { L._objective = case objExpr of L.Linear m -> L.Linear ((* objMultiplier) <$> m)
          , L._constraints = constr'
          , L._bounds = definfbounds <> convBounds bnds  -- note: left-biased union
          }
    in unlimpify . fst <$> L.branch (fmap L.assignment . L.simplex . L.standard) program
    where
      allvars (L.Linear mp) = lefts (Map.keys mp)
      allvarsC (L.Constraint l) = concatMap (\(L.C1 _ e _) -> allvars e) l

normaliseConstr :: Ord (BackendVar op) => Int -> Constraint op -> [L.Constraint1 (Var op) Void L.IntDouble]
normaliseConstr n (e1 :<= e2) =
  let (L.Linear e1', e1Const) = exprToLinear n e1
      (L.Linear e2', e2Const) = exprToLinear n e2
      -- e1' + e1Const <= e2' + e2Const
      -- e1' - e2' <= e2Const - e1Const
  in [L.C1 Nothing
           (L.Linear (Map.unionWith (+) e1' (negate <$> e2')))
           (Just (fromIntegral (e2Const - e1Const)))]
normaliseConstr n (c1 :&& c2) = normaliseConstr n c1 ++ normaliseConstr n c2
normaliseConstr n (e1 :>= e2) = normaliseConstr n (e2 :<= e1)
normaliseConstr n (e1 :== e2) = normaliseConstr n ((e1 :<= e2) :&& (e2 :<= e1))
normaliseConstr _ TrueConstraint = []

exprToLinear :: Ord (BackendVar op) => Int -> Expression op -> (L.Linear (Var op) Void L.IntDouble, Int)
exprToLinear n expr =
  let (l, cnst) = normaliseExpr n expr
  in (L.Linear (Map.fromList (map (bimap Left fromIntegral) l)), cnst)

normaliseExpr :: Int -> Expression op -> ([(Var op, Int)], Int)
normaliseExpr n (Constant (Number f)) = ([], f n)
normaliseExpr n (e1 :+ e2) = (+) <$> normaliseExpr n e1 <*> normaliseExpr n e2
normaliseExpr n (Number f :* var) = ([(var, f n)], 0)

convBounds :: Ord (BackendVar op) => Bounds op -> Map (Either (Var op) Void) (Maybe (L.R L.IntDouble), Maybe (L.R L.IntDouble))
convBounds (Binary v) = Map.singleton (Left v) (Just 0, Just 1)
convBounds (LowerUpper a v b) = Map.singleton (Left v) (Just (fromIntegral a), Just (fromIntegral b))
convBounds (Lower a v) = Map.singleton (Left v) (Just (fromIntegral a), Nothing)
convBounds (Upper v b) = Map.singleton (Left v) (Nothing, Just (fromIntegral b))
convBounds NoBounds = mempty
convBounds (a :<> b) = Map.unionWith (bimap2 (combine max) (combine min)) (convBounds a) (convBounds b)
  where bimap2 f g (x, y) (x', y') = (f x x', g y y')
        combine _ Nothing x = x
        combine _ x Nothing = x
        combine g (Just x) (Just y) = Just (g x y)

unlimpify :: L.Assignment (Var op) Void L.IntDouble -> Solution op
unlimpify (L.Assignment zvarmap rvarmap)
  | Map.null rvarmap = Map.map (\(L.Z x) -> x) zvarmap
  | otherwise = error "Real variables found in Limp ILP solution"
