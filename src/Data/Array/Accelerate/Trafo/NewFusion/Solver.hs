{-# LANGUAGE GADTs                 #-}

module Data.Array.Accelerate.Trafo.NewFusion.Solver {- (export list) -} where

import Data.Array.Accelerate.Trafo.NewFusion.AST
import Data.Array.Accelerate.AST hiding (PreOpenAcc(..))
import Data.Bifunctor

data DirectedAcyclicGraph = DAG 
  { nodes :: [(NodeId, NodeType)]
  , deps :: [(NodeId, NodeId)] -- the nodes with these id's must obey this partial order in the fusion, and fusing them will give the associated profit
  , fpes :: [(NodeId, NodeId)] -- fusion preventing edges; these nodes can't be in the same partition
  }

--TODO maybe annotate with the dimensionality
data NodeType = NodeT | UnfusableT | GenerateT | MapT | ZipWithT | FoldT | ScanLT | PermuteT | BackpermuteT

makeGraph :: LabelledOpenAcc aenv a -> [NodeId] -> DirectedAcyclicGraph -> (NodeId, DirectedAcyclicGraph)
makeGraph (LabelledOpenAcc acc) env dag = case acc of
  Alet lhs bnd body -> uncurry (makeGraph body) . first (applyLHS lhs env) $ makeGraph bnd env dag
  Variable n x -> (n, dag {nodes = (n, NodeT):nodes dag, 
                           deps = (getNodeID env x, n):deps dag} )
  Apply n f x -> let (n', dag') = makeGraphAF f env n dag in (n, dag' {nodes = (n, NodeT):nodes dag, 
                                                              deps = (n, n') : deps dag,
                                                              fpes = (getNodeID env x, n) : fpes dag})
  Aforeign n _ _ x -> (n, dag {nodes = (n, UnfusableT):nodes dag,
                               fpes = (getNodeID env x, n):fpes dag})
  Acond n e acc1 acc2 -> let dagE = makeGraphE e env dag n
                             (n1, dag1) = makeGraph acc1 env dagE
                             (n2, dag2) = makeGraph acc2 env dag1 in
                               (n, dag2 {nodes = (n, UnfusableT) : nodes dag2,
                                fpes = (n, n1) : (n, n2) : fpes dag2})
  Awhile n f g x -> let (nf, dagF) = makeGraphAF f env n dag
                        (ng, dagG) = makeGraphAF g env nf dagF in
                          (n, dagG {nodes = (n, UnfusableT) : nodes dagG,
                           fpes = (n, nf) : (nf, ng) : (getNodeID env x, n) : fpes dagG})
  Use n _ -> (n, dag {nodes = (n, NodeT) : nodes dag})
  Unit n e -> let dagE = makeGraphE e env dag n in (n, dagE {nodes = (n, NodeT) : nodes dagE})
  --TODO fuse reshape when possible
  Reshape n e x -> let dagE = makeGraphE e env dag n in (n, dagE {nodes = (n, UnfusableT) : nodes dagE,
                                fpes = (getNodeID env x, n) : fpes dagE})
  Generate n e f -> let dagE = makeGraphE e env dag n
                        dagF = makeGraphF f env dagE n in
                          (n, dagF {nodes = (n, GenerateT) : nodes dagF})
  --TODO slice
  Map n f x -> let dagF = makeGraphF f env dag n in
                    (n, dagF {nodes = (n, MapT) : nodes dagF,
                        deps = (getNodeID env x, n) : deps dagF})
  ZipWith n f x y -> let dagF = makeGraphF f env dag n in
                          (n, dagF {nodes = (n, ZipWithT) : nodes dagF,
                          deps = (getNodeID env x, n) : (getNodeID env y, n) : deps dagF})
  Fold n f e x -> let dagF = makeGraphF f env dag n
                      dagE = makeGraphE e env dagF n in
                        (n, dagE {nodes = (n, FoldT) : nodes dagE,
                        deps = (getNodeID env x, n) : deps dagE})
  -- TODO fold1, foldSeg, fold1Seg
  Scanl n f e x -> let dagF = makeGraphF f env dag n
                       dagE = makeGraphE e env dagF n in
                        (n, dagE {nodes = (n, ScanLT) : nodes dagE,
                        deps = (getNodeID env x, n) : deps dagE})
  -- TODO scanl', scanl1, scanr, scanr', scanr1
  Permute n f x g y -> let dagF = makeGraphF f env dag n
                           dagG = makeGraphF g env dagF n in
                            (n, dagG {nodes = (n, PermuteT) : nodes dagG,
                            deps = (getNodeID env x, n) : deps dagG,
                            fpes = (getNodeID env y, n) : fpes dagG})
  Backpermute n e f x -> let dagE = makeGraphE e env dag n
                             dagF = makeGraphF f env dagE n in
                              (n, dagF {nodes = (n, BackpermuteT) : nodes dagF,
                              deps = (getNodeID env x, n) : deps dagF}) 
  -- TODO stencil, stencil2                                                     
  _ -> undefined


makeGraphAF :: PreOpenAfun LabelledOpenAcc aenv a -> [NodeId] -> NodeId -> DirectedAcyclicGraph -> (NodeId, DirectedAcyclicGraph)
makeGraphAF (Alam lhs body) env n dag = makeGraphAF body (applyLHS lhs env n) n dag
makeGraphAF (Abody body) env _ dag = makeGraph body env dag

--we're in an expression, so in a single Node, so we want to know the deps of this node. Just traverse the Exp and look for 'index' and 'linearindex' to add fpe's
makeGraphE :: LabelledOpenExp env aenv a -> [NodeId] -> DirectedAcyclicGraph -> NodeId -> DirectedAcyclicGraph
makeGraphE = undefined
--like above
makeGraphF :: LabelledOpenFun env aenv a -> [NodeId] -> DirectedAcyclicGraph -> NodeId -> DirectedAcyclicGraph
makeGraphF = undefined



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


{-ILP with, for each vertically/diagonally fusable edge, (X) binary variables:
-are fused in unknown order (see backpermute)
-are fused in fold-like shape
-are fused in (..)-like shape

Horizontal fusion is allowed whenever both sides consume the same input in the same order/shape
  (many nodes can consume in 'any shape')

-}


{-consumes its input in X order:
no input: generate, use
any order: permute
same order as output: map, zipWith (but both orders have to be identical, or one has to be unfused)
unknown order (only works if input is produced in 'any order'): backpermute, foldSeg, fold1Seg
fold-scan-like: fold, fold1, scanl, scanl1, scanl', scanr, scanr1, scanr'
impossible to fuse (input has to be manifest): foreign, while, conditional, stencil, (stencil2?)
-}

{-produces its output in X order:
any order: generate, backpermute, stencil, (stencil2?)
same order as input: map, zipWith
unknown order: foldseg, fold1seg
fold-like: fold, fold1
scan-like: scanl, scanl1, scanl', scanr, scanr1, scanr'
impossible to fuse (output has to be manifest): permute, foreign, while, conditional (with conditional, `could` fuse the output distributively...)
-}


--fold-like: each threadblock cooperatively reads, processes and reduces a stripe of the input, then do a parallel reduction, then once only 1 block remains a single threadblock reduces it (and combines with initial element).

--foldseg-like: comparable to above, except for the segments.. A dynamically scheduled queue offloads work to the available threads.

--scan-like: 1) each threadblock scans a part of the array. 2) one threadblock scans the final elements of these scans, to come up with the offsets. 3) each threadblock appends the offset to each element of the result
  -- this is close to a fold, and perhaps fusing it with a fold is 'sometimes beneficial': it makes the fold itself more expensive to perform it 'like a scan', but only slightly.
    -- hard to say, ask trev

--stencil-like: fusing 'into' stencils duplicates work, so only good if input is cheap to compute.
  --works just like map, so can fuse into anything(?)




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
each x_i has an associated y_i representing the OUTPUT shape: see X in foldDim discussion. 0 means 'like foldAll' and -1 means 'unknown shape' (see backpermute)
Also a l_i, for left-to-right or right-to-left (see scans).



ILP constraints:

acyclic, precedence-preserving:
   x_{i,j} ≤ pi_j − pi_i ≤ N*x_{i,j} (with an edge from i to j)
−N*x_{i,j} ≤ pi_j - pi_i ≤ N*x_{i,j} (with no edge from i to j)

1 ≤ pi_j - pi_i

x_{i,j} = 1 (for fusion-preventing edges from i to j)

(a condition for c_i)

for Accelerate:
A bunch of rules relating the shapes to the x_i's (if node j is a map, -max*x_{i,j} ≤ y_i-y_j ≤ max*x_{i,j})
-}