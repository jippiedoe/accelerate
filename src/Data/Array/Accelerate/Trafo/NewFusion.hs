--{-# LANGUAGE DataKinds #-}
--{-# LANGUAGE KindSignatures #-}



module Data.Array.Accelerate.Trafo.NewFusion {- (export list) -} where

import Data.Array.Accelerate.AST


doAllFusion :: OpenAcc () a -> FusedAcc () a
doAllFusion openacc = fusedacc
    where
        letboundacc = letBindEverything openacc
        graph = makeGraph letboundacc
        partition = orderPartition graph $ makePartition graph
        groupedacc = rewriteAST letboundacc partition
        fusedacc = finalizeFusion groupedacc

-- "hope the environment works with me"

-- (agressively rewrite AST such that everything gets let-bound) not sure if needed, but sounds easier
-- convert AST into some graph representation, representing the partial ordering imposed by the used environment 
-- (which is way less strict then the naive one, where 'let X in Y' translates to everything in X being < everything in Y)
-- determine optimal clustering on graph
-- optimal clustering is a grouping of nodes, where the groups ordering honours the partial ordering of the AST
-- Then, rewrite the AST so all nodes in a group are let-bound together and without any nodes from outside of the group.
-- If everything went well so far, this is possible!
-- Perform the fusion within each grouping.

{-
let bind everything
openacc aenv a -> letboudacc aenv a

generate a graph (more work than it seems, but not too hard) (again, the environment could help us out here)
LabelledLetBoundAcc () a -> graph

generate and solve an ilp, for example
graph -> partition

maybe useful:
graph -> partition -> partial ordering on partition
    this would allow making a 'target AST' that simply enumerates the partition
    but that might not be relevant/ueseful
    it also just gives us safety guarantees for all the strengthening that needs to be done, probably
        but to actually perform those strengthenings we have to re-prove them on the env

rewrite ast by floating let bindings, but also sometimes sinking them, which is more difficult :(
if we work on preOpenAcc, the environment and idx's can tell us all we need to know about the safety of these transformations but they also make them hard to execute
The partial ordering on the partitions should also be able to tell us about the safety of all the strictly neccesary sinking
To seperate work a bit, just group them together (preferably honoring the partial order amongst themselves, to keep it typecorrect)
LabelledLetBoundAcc -> partition -> groupedLabelledLetBoundAcc
    groupedLabelledLetBoundAcc should just contain one extra construct, "everything below this in the AST is a single fusion group"

assign the horizontal/vertical/diagonal fusions
group -> fusedgroup
-}


data LabelledLetBoundAcc aenv a = LabelledLetBoundAcc ()
data GroupedLabelledLetBoundAcc aenv a = GroupedLabelledLetBoundAcc ()
data FusedAcc aenv a = FusedAcc ()

letBindEverything :: OpenAcc aenv a -> LabelledLetBoundAcc aenv a
letBindEverything = undefined

makeGraph :: LabelledLetBoundAcc () a -> DirectedAcyclicGraph
makeGraph = undefined

makePartition :: DirectedAcyclicGraph -> [[NodeId]]
makePartition = undefined

orderPartition :: DirectedAcyclicGraph -> [[NodeId]] -> [[NodeId]]
orderPartition = undefined

rewriteAST :: LabelledLetBoundAcc aenv a -> [[NodeId]] -> GroupedLabelledLetBoundAcc aenv a
rewriteAST = undefined

finalizeFusion :: GroupedLabelledLetBoundAcc aenv a -> FusedAcc aenv a
finalizeFusion = undefined

data DirectedAcyclicGraph = DAG 
    { nodes :: [NodeId]
    , dependencies :: [(NodeId, NodeId, Int)] -- the nodes with these id's must obey this partial order in the fusion, and fusing them will give the associated profit
    , fusionPreventingEdges :: [(NodeId, NodeId)] -- these nodes can't be in the same partition
    }

   
data DirectedAcyclicGraphAcc aenv a = DAGAcc NodeId (PreOpenAcc DirectedAcyclicGraphAcc aenv a)

newtype NodeId = NodeId Int




{-
ALet: special case
AVar, APair, ANil, Apply, AForeign, ACond, AWhile, Use, Unit, Reshape, replicate, slice: ?
producers: Generate, transform, map, zipwith (in one or two inputs?): in all directions, with almost anything
backpermute is a producer, but only if the input is the target shape. It can't vertically happen after non-producers, but can vertically happen before anything.
Permute is the opposite: fuses vertically after anything, but not before.
fold(1)(Seg): in all directions with producers and with other folds
scan(l/r)(1)('): in all directions with producers and with other scans
permute: in all directions with producers and with other permutes
stencil(2): in all directions with producers and with other stencils
-}

