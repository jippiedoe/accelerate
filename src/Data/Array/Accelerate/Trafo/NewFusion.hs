module Data.Array.Accelerate.Trafo.NewFusion {- (export list) -} where


import Data.Array.Accelerate.Trafo.NewFusion.AST
import Control.Monad.State
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.NewFusion.LetBind

doFusion :: Acc a -> FusedAcc a
doFusion acc = fusedacc
  where
    letboundacc = letBindEverything acc
    graph = makeGraph letboundacc
    partition = orderPartition graph $ makePartition graph
    groupedacc = rewriteAST letboundacc partition
    fusedacc = finalizeFusion groupedacc


letBindEverything :: Acc a -> LabelledAcc a
letBindEverything acc = evalState (letBindAcc acc) 1

makeGraph :: LabelledAcc a -> DirectedAcyclicGraph
makeGraph = undefined

-- makes the ILP and calls the solver.
makePartition :: DirectedAcyclicGraph -> [[NodeId]]
makePartition = undefined

orderPartition :: DirectedAcyclicGraph -> [[NodeId]] -> [[NodeId]]
orderPartition = undefined

rewriteAST :: LabelledOpenAcc aenv a -> [[NodeId]] -> GroupedLabelledAcc aenv a
rewriteAST = undefined

finalizeFusion :: GroupedLabelledAcc () a -> FusedAcc a
finalizeFusion = undefined

data DirectedAcyclicGraph = DAG 
  { nodes :: [NodeId]
  , dependencies :: [(NodeId, NodeId, Int)] -- the nodes with these id's must obey this partial order in the fusion, and fusing them will give the associated profit
  , fusionPreventingEdges :: [(NodeId, NodeId)] -- these nodes can't be in the same partition
  }


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
unknown order (only works if input is produced in 'any order'): backpermute
fold-like: fold, fold1
foldseg-like: foldSeg, fold1Seg
scan-like: scanl, scanl1, scanl', scanr, scanr1, scanr'
stencil-like: stencil, (stencil2?)
impossible to fuse (input has to be manifest): foreign, while, conditional 
-}

{-produces its output in X order:
any order: generate, backpermute
same order as input: map, zipWith
fold-like: fold, fold1
foldseg-like: foldseg, fold1seg
scan-like: scanl, scanl1, scanl', scanr, scanr1, scanr'
stencil-like: stencil, (stencil2?)
impossible to fuse (output has to be manifest): permute, foreign, while, conditional (with conditional, `could` fuse the output distributively...)
-}


--fold-like: each threadblock cooperatively reads, processes and reduces a stripe of the input, then do a parallel reduction, then once only 1 block remains a single threadblock reduces it (and combines with initial element).

--foldseg-like: comparable to above, except for the segments.. A dynamically scheduled queue offloads work to the available threads.

--scan-like: 1) each threadblock scans a part of the array. 2) one threadblock scans the final elements of these scans, to come up with the offsets. 3) each threadblock appends the offset to each element of the result
  -- this is close to a fold, and perhaps fusing it with a fold is 'sometimes beneficial': it makes the fold itself more expensive to perform it 'like a scan', but only slightly.
    -- hard to say, ask trev

--stencil-like: fusing 'into' stencils duplicates work, so only good if input is cheap to compute.
  --works just like map, so can fuse into anything(?)