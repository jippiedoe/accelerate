{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph, Construction, makeFullGraphF, Graph, backendConstruc ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, splitExecs, ClusterLs ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering
    ( reconstruct, reconstructF )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc, PartitionedAfun, Cluster)
import Data.Array.Accelerate.AST.Operation
    ( OperationAcc, OperationAfun )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( MIPProvider, cbc, cplex, glpsol, gurobiCl, lpSolve, scip )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp
    ( LimpProvider )

import System.IO.Unsafe (unsafePerformIO)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Map (Map)
import Data.Proxy (Proxy(..))
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Function ((&))


cbcFusion, gurobiFusion, cplexFusion, glpsolFusion, lpSolveFusion, scipFusion, limpFusion
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => OperationAcc op () a -> PartitionedAcc op () a
cbcFusion     = ilpFusion (Proxy @MIPProvider) cbc
gurobiFusion  = ilpFusion (Proxy @MIPProvider) gurobiCl
cplexFusion   = ilpFusion (Proxy @MIPProvider) cplex
glpsolFusion  = ilpFusion (Proxy @MIPProvider) glpsol
lpSolveFusion = ilpFusion (Proxy @MIPProvider) lpSolve
scipFusion    = ilpFusion (Proxy @MIPProvider) scip
limpFusion    = ilpFusion (Proxy @LimpProvider) ()

cbcFusionF, gurobiFusionF, cplexFusionF, glpsolFusionF, lpSolveFusionF, scipFusionF, limpFusionF
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => OperationAfun op () a -> PartitionedAfun op () a
cbcFusionF     = ilpFusionF (Proxy @MIPProvider) cbc
gurobiFusionF  = ilpFusionF (Proxy @MIPProvider) gurobiCl
cplexFusionF   = ilpFusionF (Proxy @MIPProvider) cplex
glpsolFusionF  = ilpFusionF (Proxy @MIPProvider) glpsol
lpSolveFusionF = ilpFusionF (Proxy @MIPProvider) lpSolve
scipFusionF    = ilpFusionF (Proxy @MIPProvider) scip
limpFusionF    = ilpFusionF (Proxy @LimpProvider) ()

ilpFusion  :: (MakesILP op, ILPSolver provider s op, Pretty.PrettyOp (Cluster op)) => Proxy provider -> s -> OperationAcc  op () a -> PartitionedAcc op () a
ilpFusion  = ilpFusion' makeFullGraph  reconstruct

ilpFusionF :: (MakesILP op, ILPSolver provider s op, Pretty.PrettyOp (Cluster op)) => Proxy provider -> s -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF = ilpFusion' makeFullGraphF reconstructF

ilpFusion' :: (MakesILP op, ILPSolver provider s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> Proxy provider
           -> s 
           -> x 
           -> y
ilpFusion' k1 k2 provider s acc = fusedAcc
  where
    (info@(Info graph _ _), constrM') = k1 acc
    constrM = backendConstruc solution constrM'
    ilp                               = makeILP info
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve provider s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

