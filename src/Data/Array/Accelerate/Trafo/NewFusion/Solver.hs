{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Array.Accelerate.Trafo.NewFusion.Solver {- (export list) -} where

import Data.Array.Accelerate.Trafo.NewFusion.AST hiding (PreFusedOpenAcc(..))
import Data.Array.Accelerate.AST hiding (PreOpenAcc(..))
import Data.Bifunctor
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Control.Monad.LPMonad
import Data.LinearProgram
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar


makeGraph :: LabelledOpenAcc aenv a -> [NodeId] -> DirectedAcyclicGraph -> (NodeId, DirectedAcyclicGraph)
makeGraph (LabelledOpenAcc acc) env dag = case acc of
  Alet lhs bnd body -> uncurry (makeGraph body) . first (applyLHS lhs env) $ makeGraph bnd env dag
  Variable n x -> (n, dag {nodes = (n, MapT (getNodeID env x)) $: nodes dag}) -- map is the canonical example of something which fuses every way
  Apply n f x -> let (_, dag') = makeGraphAF f env n dag in
                     (n, dag' {nodes = (n, UnfusableT (getNodeID env x)) $: nodes dag,
                               fpes = (getNodeID env x, n) : fpes dag})
  Aforeign n _ _ x -> (n, dag {nodes = (n, UnfusableT (getNodeID env x)) $: nodes dag,
                               fpes = (getNodeID env x, n):fpes dag})
  Acond n e acc1 acc2 -> let dagE = makeGraphE e env dag n
                             (n1, dag1) = makeGraph acc1 env dagE
                             (n2, dag2) = makeGraph acc2 env dag1 in
                               (n, dag2 {nodes = (n, UnfusableT n1) $: nodes dag2,
                                fpes = (n, n1) : (n, n2) : fpes dag2})
  Awhile n f g x -> let (nf, dagF) = makeGraphAF f env n dag
                        (ng, dagG) = makeGraphAF g env nf dagF in
                          (n, dagG {nodes = (n, UnfusableT nf) $: nodes dagG,
                           fpes = (n, nf) : (nf, ng) : (getNodeID env x, n) : fpes dagG})
  Use n _ -> (n, dag {nodes = (n, UnfusableT n) $: nodes dag})
  Unit n e -> let dagE = makeGraphE e env dag n in (n, dagE {nodes = (n, UnfusableT n) $: nodes dagE})
  --TODO fuse reshape when possible
  Reshape n e x -> let dagE = makeGraphE e env dag n in (n, dagE {nodes = (n, UnfusableT (getNodeID env x)) $: nodes dagE,
                                fpes = (getNodeID env x, n) : fpes dagE})
  Generate n e f -> let dagE = makeGraphE e env dag n
                        dagF = makeGraphF f env dagE n in
                          (n, dagF {nodes = (n, GenerateT) $: nodes dagF})
  --TODO slice
  Map n f x -> let dagF = makeGraphF f env dag n in
                    (n, dagF {nodes = (n, MapT (getNodeID env x)) $: nodes dagF})
  ZipWith n f x y -> let dagF = makeGraphF f env dag n in
                          (n, dagF {nodes = (n, ZipWithT (getNodeID env x) (getNodeID env y)) $: nodes dagF})
  Fold n f e (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z ->
        let dagF = makeGraphF f env dag n
            dagE = makeGraphE e env dagF n in
              (n, dagE {nodes = (n, FoldFlatT (getNodeID env x)) $: nodes dagE})
    | otherwise ->
        let dagF = makeGraphF f env dag n
            dagE = makeGraphE e env dagF n in
              (n, dagE {nodes = (n, FoldDimT (getNodeID env x)) $: nodes dagE})
  -- TODO fold1, foldSeg, fold1Seg
  Scanl n f e (x :: ArrayVars aenv (Array (sh:.Int) e))
   | Just Refl <- matchShapeType @sh @Z ->
        let dagF = makeGraphF f env dag n
            dagE = makeGraphE e env dagF n in
              (n, dagE {nodes = (n, ScanFlatT (getNodeID env x) False) $: nodes dagE})
   | otherwise ->
        let dagF = makeGraphF f env dag n
            dagE = makeGraphE e env dagF n in
              (n, dagE {nodes = (n, ScanFlatT (getNodeID env x) False) $: nodes dagE})
  -- TODO scanl', scanl1, scanr, scanr', scanr1
  Permute n f x g y -> let dagF = makeGraphF f env dag n
                           dagG = makeGraphF g env dagF n in
                            (n, dagG {nodes = (n, PermuteT (getNodeID env x) (getNodeID env y)) $: nodes dagG,
                            fpes = (getNodeID env y, n) : fpes dagG})
  Backpermute n e f x -> let dagE = makeGraphE e env dag n
                             dagF = makeGraphF f env dagE n in
                              (n, dagF {nodes = (n, BackpermuteT (getNodeID env x)) $: nodes dagF})
  -- TODO stencil, stencil2
  _ -> undefined


makeGraphAF :: PreOpenAfun LabelledOpenAcc aenv a -> [NodeId] -> NodeId -> DirectedAcyclicGraph -> (NodeId, DirectedAcyclicGraph)
makeGraphAF (Alam lhs body) env n dag = makeGraphAF body (applyLHS lhs env n) n dag
makeGraphAF (Abody body) env _ dag = makeGraph body env dag

--we're in an expression, so in a single Node, so we want to know the deps of this node. Just traverse the Exp and look for 'index' and 'linearindex' to add fpe's
makeGraphE :: LabelledOpenExp env aenv a -> [NodeId] -> DirectedAcyclicGraph -> NodeId -> DirectedAcyclicGraph
makeGraphE expr env dag n = case expr of
  Index       (LabelledOpenAcc (Variable _ a)) sh -> let dag' = makeGraphE sh env dag n in dag' {fpes = (getNodeID env a, n) : fpes dag'}
  LinearIndex (LabelledOpenAcc (Variable _ a)) i  -> let dag' = makeGraphE i  env dag n in dag' {fpes = (getNodeID env a, n) : fpes dag'}
  Index _ _       -> error "fml"
  LinearIndex _ _ -> error "fml"
  _ -> dag


--like makeGraphE
makeGraphF :: LabelledOpenFun env aenv a -> [NodeId] -> DirectedAcyclicGraph -> NodeId -> DirectedAcyclicGraph
makeGraphF _ _ dag _= dag

($:) :: (NodeId, NodeType) -> IM.IntMap NodeType -> IM.IntMap NodeType
($:) (NodeId n, x) = IM.insert n x

-- given a list representing "env", and one representing "a", make a list representing "env'"
applyLHS :: LeftHandSide a env env'
         -> [NodeId] -- env
         -> NodeId -- a
         -> [NodeId] -- env'
applyLHS LeftHandSideArray env a = a : env
applyLHS (LeftHandSideWildcard _) env _ = env
applyLHS (LeftHandSidePair lhs1 lhs2) env a = let env' = applyLHS lhs1 env a in applyLHS lhs2 env' a

getNodeID :: [NodeId] -> ArrayVars env a -> NodeId
getNodeID _ ArrayVarsNil = NodeId 0 -- all other node ID's are positive, and we can later filter out the 0's as no computation is neccesary to construct a Nil
getNodeID (n:_) (ArrayVarsArray (ArrayVar ZeroIdx)) = n
getNodeID (_:ns) (ArrayVarsArray (ArrayVar (SuccIdx idx))) = getNodeID ns $ ArrayVarsArray (ArrayVar idx)
getNodeID ns (ArrayVarsPair a1 a2) = let n1 = getNodeID ns a1; n2 = getNodeID ns a2 in if n1==n2 then n1 else error "inconsistent environment at newfusion/solver.hs" -- TODO once it works, remove this check
getNodeID [] _ = error "NewFusion/Solver.hs: empty environment"






-- for Scans, we ignore the ' variant (which returns both the prefix sums and the final sum as two separate arrays of different dimensions) for now
-- for Scans, 'False' is left-to-right (corresponding to 0 in the ILP)
data NodeType = GenerateT | MapT NodeId | ZipWithT NodeId NodeId | FoldDimT NodeId
              | FoldFlatT NodeId | ScanDimT NodeId Bool | ScanFlatT NodeId Bool
              | PermuteT NodeId NodeId | BackpermuteT NodeId | UnfusableT NodeId
              | StencilT NodeId | Stencil2T NodeId NodeId


-- The intmap contains a minimal description of node (NodeId i) at index i.
-- The list contains the fusion preventing edges.
data DirectedAcyclicGraph = DAG {
  nodes :: IM.IntMap NodeType,
  fpes :: [(NodeId, NodeId)]}

data ILPVar = Fusion NodeId   NodeId -- 0 means fused, 1 means not fused (not in the same fusion group)
            | Pi              NodeId -- the number of the fusion group this node is in, used for acyclicity
            | InputShape      NodeId -- -2 represents 'unknown' (backpermute output), -1 represents an even spread across all blocks, X>=0 means each threadblock holds every value along the innermost X dimensions (X=1 represents the current FoldDim approach, and X=0 means each threadblock holds only 1 value)
            | OutputShape     NodeId
            | InputDirection  NodeId -- 0 is ->, 1 is <-, 2 is 'unknown'
            | OutputDirection NodeId deriving (Eq, Ord, Show)





-- The LPM `monad' is a State (LinearProgram variables values) ()
-- We write the LP by using functions like mapM_ to modify the state while discarding the () result
makeILP :: DirectedAcyclicGraph -> LP ILPVar Int
makeILP DAG{..} = execLPM $ do
  let verticals = concatMap makeVerticals nodes'
  let horizontals = makeHorizontals verticals
  let verticalVars = map (uncurry Fusion) verticals
  let horizontalVars = map (uncurry Fusion) horizontals
  let fusionVars = verticalVars ++ horizontalVars
  let fpeVars = map (uncurry Fusion) fpes
  let piVars = map (Pi . fst) nodes'

  setDirection Min -- minimise cost function
  setObjective $ linCombination $ map (1,) fusionVars -- cost function, currently minimising the number of unfused edges

  -- fusion variables
  mapM_ (\x -> varBds x 0 1) fusionVars

  -- 'pi' variables for acyclicity
  mapM_ (\x -> varBds x 0 (length nodes)) piVars

  -- fpe constraints
  mapM_ (`varEq` 1) fpeVars

  -- acyclicity contraints
  mapM_ makeAcyclicV (verticalVars ++ fpeVars)
  mapM_ makeAcyclicH horizontalVars

  -- nodetype-specific constraints:
  -- - input and output shape and direction variables
  mapM_ makeConstraint nodes'
  -- - rules relating those variables to the fusion variables
  mapM_ fusionShapeV verticalVars
  mapM_ fusionShapeH horizontalVars

  where
    nodes' :: [(NodeId, NodeType)]
    nodes' = map (first NodeId) (IM.assocs nodes)

    -- the maximum number of innermost dimensions a threadblock may hold, for a fold or scan on multidimensional data
    maxFoldScanDims :: Int
    maxFoldScanDims = 5

    -- All the fusion variables for vertical fusion, (x,y) means that y consumes x
    makeVerticals :: (NodeId, NodeType) -> [(NodeId, NodeId)]
    makeVerticals (x, nodetype) = case nodetype of
      UnfusableT _     -> []
      GenerateT        -> []
      MapT         y   -> [(y, x)]
      ZipWithT     y z -> [(y, x), (z, x)]
      FoldDimT     y   -> [(y, x)]
      FoldFlatT    y   -> [(y, x)]
      ScanDimT     y _ -> [(y, x)]
      ScanFlatT    y _ -> [(y, x)]
      PermuteT     y _ -> [(y, x)] -- can't fuse with the 'target array'
      BackpermuteT y   -> [(y, x)]
      StencilT     _   -> [] -- [(y, x)]
      Stencil2T    _ _ -> [] -- [(y, x), (z, x)]

    -- given all the vertical fusion variables (where (x,y) means that the array x could be fused into the computation y),
    -- produce a list of pairs of nodeIds that both consume the same array and could thus be fused horizontally.
    -- TODO sort and remove duplicates
    makeHorizontals :: [(NodeId, NodeId)] -> [(NodeId, NodeId)]
    makeHorizontals = map (\(x,y) -> if x<y then (x,y) else (y,x)) . concatMap carthesian . M.elems . M.fromListWith (++) . map (second pure)
    carthesian :: [a] -> [(a, a)]
    carthesian [] = []
    carthesian (x:ys) = map (x,) ys ++ carthesian ys

    makeConstraint :: (NodeId, NodeType) -> LPM ILPVar Int ()
    makeConstraint (n, nodetype) = case nodetype of
      UnfusableT _ ->   do varBds (OutputDirection n) 0 2
                           varGeq (OutputShape n) (-2)
      GenerateT ->      do varBds (OutputDirection n) 0 2
                           varGeq (OutputShape n) (-2)
      MapT _    ->      do varBds (OutputDirection n) 0 1
                           varGeq (OutputShape n) (-2)
                           equalTo (linCombination [(-1, OutputDirection n), (1, InputDirection n)]) 0
                           equalTo (linCombination [(-1, OutputShape     n), (1, InputShape     n)]) 0
      ZipWithT _ _ ->   do varBds (OutputDirection n) 0 2
                           varGeq (OutputShape n) (-2)
                           equalTo (linCombination [(-1, OutputDirection n), (1, InputDirection n)]) 0
                           equalTo (linCombination [(-1, OutputShape     n), (1, InputShape     n)]) 0
      FoldDimT _ ->     do varBds (OutputDirection n) 0 2
                           varBds (OutputShape n) 0 maxFoldScanDims
                           equalTo (linCombination [(-1, OutputDirection n), (1, InputDirection n)]) 0
                           equalTo (linCombination [(-1, OutputShape     n), (1, InputShape     n)]) 1
      FoldFlatT _  ->   do varBds (InputDirection n) 0 2 -- the output of a FoldFlat is just one element, so no variables needed
                           varEq (InputShape n) (-1)
      ScanDimT _ b ->   do varEq (OutputDirection n) (fromEnum b)
                           varBds (OutputShape n) 1 maxFoldScanDims
                           equalTo (linCombination [(-1, OutputDirection n), (1, InputDirection n)]) 0
                           equalTo (linCombination [(-1, OutputShape     n), (1, InputShape     n)]) 0
      ScanFlatT _ b ->  do varEq (InputDirection n) (fromEnum b)
                           varEq (InputShape n) (-1)
                           equalTo (linCombination [(-1, OutputDirection n), (1, InputDirection n)]) 0
                           equalTo (linCombination [(-1, OutputShape     n), (1, InputShape     n)]) 0
      PermuteT _ _ ->   do varBds (InputDirection n) 0 2 -- can't fuse the output of a permute, so no variable needed
                           varGeq (InputShape n) (-2)
      BackpermuteT _ -> do varBds (OutputDirection n) 0 2 -- the output can be any shape, but the input has to be every shape
                           varGeq (OutputShape n) (-2)
                           varEq (InputDirection n) 2
                           varEq (InputShape n) (-2)
      StencilT _ ->     do varBds (OutputDirection n) 0 2 -- for now, stencils don't fuse with their inputs so no input variables needed
                           varGeq (OutputShape n) (-2)
      Stencil2T _ _ ->  do varBds (OutputDirection n) 0 2 -- for now, stencils don't fuse with their inputs so no input variables needed
                           varGeq (OutputShape n) (-2)

    -- generate the constraints belonging to a vertical fusion: if fused, the input and output have to match
    fusionShapeV, fusionShapeH :: ILPVar -> LPM ILPVar Int ()
    fusionShapeV (Fusion x y) = do
      leqTo (linCombination [(-1, OutputDirection x), ( 1, InputDirection y), (-2, Fusion x y)]) 0 -- Because the direction is between 0 and 2, this ensures that if fused the directions are equal without imposing restrictions if not fused
      leqTo (linCombination [( 1, OutputDirection x), (-1, InputDirection y), (-2, Fusion x y)]) 0
      leqTo (linCombination [(-1, OutputShape x), ( 1, InputShape y), (-maxFoldScanDims, Fusion x y)]) 0
      leqTo (linCombination [( 1, OutputShape x), (-1, InputShape y), (-maxFoldScanDims, Fusion x y)]) 0
    fusionShapeV _ = ilpError

    -- generate the constraints belonging to a horizontal fusion: if fused, the inputs have to match
    fusionShapeH (Fusion x y) = do
      leqTo (linCombination [(-1, InputDirection x), ( 1, InputDirection y), (-2, Fusion x y)]) 0 -- Because the direction is between 0 and 2, this ensures that if fused the directions are equal without imposing restrictions if not fused
      leqTo (linCombination [( 1, InputDirection x), (-1, InputDirection y), (-2, Fusion x y)]) 0
      leqTo (linCombination [(-1, InputShape x), ( 1, InputShape y), (-maxFoldScanDims, Fusion x y)]) 0
      leqTo (linCombination [( 1, InputShape x), (-1, InputShape y), (-maxFoldScanDims, Fusion x y)]) 0
    fusionShapeH _ = ilpError


    makeAcyclicV, makeAcyclicH :: ILPVar -> LPM ILPVar Int ()
    makeAcyclicV (Fusion x y) = do
      leqTo (linCombination [(1,              Fusion x y), (-1, Pi y), ( 1, Pi x)]) 0 -- f_{x,y} ≤ pi_y − pi_x   ==> precedence-preserving
      leqTo (linCombination [(-IM.size nodes, Fusion x y), ( 1, Pi y), (-1, Pi x)]) 0 -- pi_y − pi_x ≤ N*f_{x,y} ==> guarantees that the pi's are equal if fused
    makeAcyclicV _ = ilpError

    makeAcyclicH (Fusion x y) = do
      leqTo (linCombination [(-IM.size nodes, Fusion x y), (-1, Pi y), ( 1, Pi x)]) 0 -- −N*f_{i,j} ≤ pi_y - pi_x
      leqTo (linCombination [(-IM.size nodes, Fusion x y), ( 1, Pi y), (-1, Pi x)]) 0 -- pi_y − pi_x ≤ N*f_{x,y} ==> guarantees that the pi's are equal if fused
    makeAcyclicH _ = ilpError


    ilpError = error "A function expected '(Fusion x y)' but got something else in NewFusion/Solver.hs"


callGLPK :: LP ILPVar Int -> IO Int
callGLPK lp = do
  print "res1:"
  res1 <- glpSolveVars opt1 lp
  print res1
  print "res2:"
  res2 <- glpSolveVars opt2 lp
  print res2
  return 3
  where opt1 = simplexDefaults
        opt2 = mipDefaults




-- data location options:
{-
scanDim input = scanDim output = foldDim input:  each threadblock has the innermost X dims
foldDim output                                :  each threadblock has the innermost (X-1) dims

scanAll input = scanAll output = foldAll input:  all values spread evenly (in order) across threadBLOCKS
foldAll output                                :  there is only 1 value, it's at 0


To allow more, maybe give folddim the option to have an arbitrary number of innermost dimensions per threadblock,
and output one less dimension per threadblock. Cost function should make sure to keep this within reason.

X should be part of the ILP
(if it's difficult otherwise, could make X=0 a 'magic number' representing the foldAll input
  then a single linear number is able to summarise the location of data of a multidim array)
-}











{- ILP variables:

x_{i,j} in {0,1} -> nodes i,j fused or not fused
  not for each pair: 'unrelated' nodes have no variable - unless we want to attach weight to them
  - connected nodes have the vertical/diagonal condition: can only be fused if the intermediate result is of consistent shape
  - sibling nodes have the horizontal condition: can only be fused if the inputshape is consistent

for acyclicity:
pi_i in Z -> node i is in cluster n

(for cost model: --this was in Amos Robinson
c_i in {0,1} -> the output of i is `internal' in the cluster pi_i)

for Accelerate:
each x_i has an associated y_i representing the INPUT shape and a z_i representing the OUPUT shape: see X in foldDim discussion. 0 means 'like foldAll' and -1 means 'unknown shape' (see backpermute)
Also a lin_i and lout_i, for left-to-right or right-to-left (see scans).



ILP constraints:

1 ≤ pi_j - pi_i

x_{i,j} = 1 (for fusion-preventing edges from i to j)

(a condition for c_i)

for Accelerate:
A bunch of rules relating the shapes to the x_i's (if node j is a map, -max*x_{i,j} ≤ y_i-y_j ≤ max*x_{i,j})
-}