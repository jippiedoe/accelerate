{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Array.Accelerate.Trafo.NewFusion.Solver
  ( makeGraph
  , DirectedAcyclicGraph(..)
  , makeILP
  , callGLPK
  , callGLPKTest
  , groupNodes
  )
where

import           Data.Array.Accelerate.Trafo.NewFusion.AST
                                         hiding ( PreFusedOpenAcc(..) )
import           Data.Array.Accelerate.AST
                                         hiding ( PreOpenAcc(..) )
import           Data.Bifunctor
import qualified Data.IntMap.Strict            as IM
import qualified Data.Map.Strict               as M
import           Control.Monad.LPMonad
import           Data.LinearProgram      hiding ( (*) )
import           Data.Array.Accelerate.Analysis.Match
import           Data.Array.Accelerate.Array.Sugar
import           Data.List
import           Data.Function

-- TODO fold output can have any direction

makeGraph
  :: LabelledOpenAcc aenv a
  -> [NodeId]
  -> DirectedAcyclicGraph
  -> (NodeId, DirectedAcyclicGraph)
makeGraph (LabelledOpenAcc acc) env dag = case acc of
  Alet lhs bnd body ->
    uncurry (makeGraph body) . first (applyLHS lhs env) $ makeGraph bnd env dag
  Variable n x ->
    ( n
    , dag { nodes = map (\n' -> (n, VarT n')) (getNodeIds env x) $++ nodes dag }
    )
  Apply n f x ->
    let (_, dag') = makeGraphAF f env n dag
    in  ( n
        , dag'
          { nodes = map (\n' -> (n, UnfusableT n')) (getNodeIds env x)
                      $++ nodes dag
          , fpes  = map (, n) (getNodeIds env x) ++ fpes dag
          }
        )
  Aforeign n _ _ x ->
    ( n
    , dag
      { nodes = map (\n' -> (n, UnfusableT n')) (getNodeIds env x) $++ nodes dag
      , fpes  = map (, n) (getNodeIds env x) ++ fpes dag
      }
    )
  Acond n e acc1 acc2 -> -- n -> e -> n1 -> n2
    let dagE       = makeGraphE e env dag n
        (n1, dag1) = makeGraph acc1 env dagE
        (n2, dag2) = makeGraph acc2 env dag1
    in  ( n
        , dag2 { nodes = (n, UnfusableT n1) $: nodes dag2
               , fpes  = (n1, n2) : fpes dag2
               }
        )
  Awhile n f g x -> -- we enforce x -> n -> ng -> nf, to prevent any fusion across the while-loop
    let (ng, dagG) = makeGraphAF g env n dag -- n -> ng
        (_ , dagF) = makeGraphAF f env ng dagG -- ng -> nf
    in  ( n
        , dagF { nodes = (n, UnfusableT (head $ getNodeIds env x)) $: nodes dagF
               , fpes  = map (, n) (getNodeIds env x) ++ fpes dagF -- x -> n
               }
        )
  Use n _ -> (n, dag { nodes = (n, GenerateT) $: nodes dag })
  Unit n e ->
    let dagE = makeGraphE e env dag n
    in  (n, dagE { nodes = (n, GenerateT) $: nodes dagE })
  --TODO figure out how Reshape works in the backend, or where it dissapears
  Reshape n e x ->
    let dagE = makeGraphE e env dag n
    in  ( n
        , dagE { nodes = (n, UnfusableT (getNodeId env x)) $: nodes dagE
               , fpes  = (getNodeId env x, n) : fpes dagE
               }
        )
  Generate n e f ->
    let dagE = makeGraphE e env dag n
        dagF = makeGraphF f env dagE n
    in  (n, dagF { nodes = (n, GenerateT) $: nodes dagF })
  Transform n e f g x -> -- should never occur, as transform is a product of old fusion
    let dagE = makeGraphE e env dag n
        dagF = makeGraphF f env dagE n
        dagG = makeGraphF g env dagF n
    in  (n, dagG { nodes = (n, MapT (getNodeId env x)) $: nodes dagG })
  Replicate n _ e x -> -- TODO make a replicateT, which is less restrictive than backpermuteT
    let dagE = makeGraphE e env dag n
    in  (n, dagE { nodes = (n, BackpermuteT (getNodeId env x)) $: nodes dagE })
  Slice n _ x e -> --TODO ignore 'slice type information'?
    let dagE = makeGraphE e env dag n
    in  (n, dagE { nodes = (n, BackpermuteT (getNodeId env x)) $: nodes dagE })
  Map n f x ->
    let dagF = makeGraphF f env dag n
    in  (n, dagF { nodes = (n, MapT (getNodeId env x)) $: nodes dagF })
  ZipWith n f x y ->
    let dagF = makeGraphF f env dag n
    in  ( n
        , dagF
          { nodes = (n, ZipWithT (getNodeId env x) (getNodeId env y))
                      $: nodes dagF
          }
        )
  Fold n f e (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
           dagE = makeGraphE e env dagF n
       in  (n, dagE { nodes = (n, FoldFlatT (getNodeId env x)) $: nodes dagE })
    | otherwise
    -> let dagF = makeGraphF f env dag n
           dagE = makeGraphE e env dagF n
       in  (n, dagE { nodes = (n, FoldDimT (getNodeId env x)) $: nodes dagE })
  Fold1 n f (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
       in  (n, dagF { nodes = (n, FoldFlatT (getNodeId env x)) $: nodes dagF })
    | otherwise
    -> let dagF = makeGraphF f env dag n
       in  (n, dagF { nodes = (n, FoldDimT (getNodeId env x)) $: nodes dagF })
  FoldSeg n f e (x :: ArrayVars aenv (Array (sh:.Int) e)) s
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
           dagE = makeGraphE e env dagF n
       in  ( n
           , dagE
             { nodes = (n, FoldSegFlatT (getNodeId env x) (getNodeId env s))
                         $: nodes dagE
             }
           )
    | otherwise
    -> let dagF = makeGraphF f env dag n
           dagE = makeGraphE e env dagF n
       in  ( n
           , dagE
             { nodes = (n, FoldSegDimT (getNodeId env x) (getNodeId env s))
                         $: nodes dagE
             }
           )
  Fold1Seg n f (x :: ArrayVars aenv (Array (sh:.Int) e)) s
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF
             { nodes = (n, FoldSegFlatT (getNodeId env x) (getNodeId env s))
                         $: nodes dagF
             }
           )
    | otherwise
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF
             { nodes = (n, FoldSegDimT (getNodeId env x) (getNodeId env s))
                         $: nodes dagF
             }
           )
  Scanl n f e (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let
         dagF = makeGraphF f env dag n
         dagE = makeGraphE e env dagF n
       in
         ( n
         , dagE { nodes = (n, ScanFlatT (getNodeId env x) False) $: nodes dagE }
         )
    | otherwise
    -> let
         dagF = makeGraphF f env dag n
         dagE = makeGraphE e env dagF n
       in
         ( n
         , dagE { nodes = (n, ScanDimT (getNodeId env x) False) $: nodes dagE }
         )
  Scanl1 n f (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF { nodes = (n, ScanFlatT (getNodeId env x) False) $: nodes dagF
                  }
           )
    | otherwise
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF { nodes = (n, ScanDimT (getNodeId env x) False) $: nodes dagF
                  }
           )
  Scanr n f e (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let
         dagF = makeGraphF f env dag n
         dagE = makeGraphE e env dagF n
       in
         ( n
         , dagE { nodes = (n, ScanFlatT (getNodeId env x) True) $: nodes dagE }
         )
    | otherwise
    -> let dagF = makeGraphF f env dag n
           dagE = makeGraphE e env dagF n
       in  ( n
           , dagE { nodes = (n, ScanDimT (getNodeId env x) True) $: nodes dagE }
           )
  Scanr1 n f (x :: ArrayVars aenv (Array (sh:.Int) e))
    | Just Refl <- matchShapeType @sh @Z
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF { nodes = (n, ScanFlatT (getNodeId env x) True) $: nodes dagF
                  }
           )
    | otherwise
    -> let dagF = makeGraphF f env dag n
       in  ( n
           , dagF { nodes = (n, ScanDimT (getNodeId env x) True) $: nodes dagF }
           )
  -- TODO scanl', scanr' are annoying, as they really already represent a vertically fused unit of a scan and slices
  Permute n f x g y ->
    let dagF = makeGraphF f env dag n
        dagG = makeGraphF g env dagF n
    in  ( n
        , dagG
          { nodes = (n, PermuteT (getNodeId env x) (getNodeId env y))
                      $: nodes dagG
          , fpes  = (getNodeId env y, n) : fpes dagG
          }
        )
  Backpermute n e f x ->
    let dagE = makeGraphE e env dag n
        dagF = makeGraphF f env dagE n
    in  (n, dagF { nodes = (n, BackpermuteT (getNodeId env x)) $: nodes dagF })
  Stencil n f b x ->
    let dagF = makeGraphF f env dag n
        dagB = makeGraphB b env dagF n
    in  (n, dagB { nodes = (n, StencilT (getNodeId env x)) $: nodes dagB })
  Stencil2 n f bx x by y ->
    let dagF  = makeGraphF f env dag n
        dagBx = makeGraphB bx env dagF n
        dagBy = makeGraphB by env dagBx n
    in  ( n
        , dagBy
          { nodes = (n, Stencil2T (getNodeId env x) (getNodeId env y))
                      $: nodes dagBy
          }
        )
  Scanl'{} -> error "I don't like scanl' and scanr'"
  Scanr'{} -> error "I don't like scanl' and scanr'"


makeGraphAF
  :: PreOpenAfun LabelledOpenAcc aenv a
  -> [NodeId]
  -> NodeId
  -> DirectedAcyclicGraph
  -> (NodeId, DirectedAcyclicGraph)
makeGraphAF (Alam lhs body) env n dag =
  makeGraphAF body (applyLHS lhs env n) n dag
makeGraphAF (Abody body) env n dag =
  let (m, dag') = makeGraph body env dag
  in  (m, dag' { fpes = (n, m) : fpes dag' })

--we're in an expression, so in a single Node, so we want to know the deps of this node. Just traverse the Exp and look for 'index' and 'linearindex' to add fpe's
makeGraphE
  :: LabelledOpenExp env aenv a
  -> [NodeId]
  -> DirectedAcyclicGraph
  -> NodeId
  -> DirectedAcyclicGraph
makeGraphE expr env dag n = case expr of
  Index (LabelledOpenAcc (Variable _ a)) sh ->
    let dag' = makeGraphE1 sh
    in  dag' { fpes = (getNodeId env a, n) : fpes dag' }
  LinearIndex (LabelledOpenAcc (Variable _ a)) i ->
    let dag' = makeGraphE1 i
    in  dag' { fpes = (getNodeId env a, n) : fpes dag' }
  Index _ _ -> error "please float array computations out of expressions"
  LinearIndex _ _ -> error "please float array computations out of expressions"

  Let         bnd body -> makeGraphE2 bnd body
  Tuple tup            -> makeGraphT tup dag
  Prj       _  t       -> makeGraphE1 t
  IndexCons sh sz      -> makeGraphE2 sh sz
  IndexHead sh         -> makeGraphE1 sh
  IndexTail sh         -> makeGraphE1 sh
  IndexSlice _ ix sh   -> makeGraphE2 ix sh
  IndexFull  _ ix sl   -> makeGraphE2 ix sl
  ToIndex   sh ix      -> makeGraphE2 sh ix
  FromIndex sh ix      -> makeGraphE2 sh ix
  Cond  p t e          -> makeGraphE p env (makeGraphE2 t e) n
  While p f x -> makeGraphF p env (makeGraphF f env (makeGraphE1 x) n) n
  PrimApp _ x          -> makeGraphE1 x
  Shape     _          -> dag --shape information can be inferred without constraints on fusion? TODO check
  ShapeSize sh         -> makeGraphE1 sh
  Intersect s t        -> makeGraphE2 s t
  Union     s t        -> makeGraphE2 s t
  Foreign _ f e        -> makeGraphF f env (makeGraphE1 e) n
  Coerce e             -> makeGraphE1 e
  _                    -> dag -- Var, Const, Undef, IndexNil, IndexAny, PrimConst
 where
  makeGraphT
    :: Tuple (LabelledOpenExp env aenv) t
    -> DirectedAcyclicGraph
    -> DirectedAcyclicGraph
  makeGraphT NilTup        dag' = dag'
  makeGraphT (SnocTup t e) dag' = makeGraphT t $ makeGraphE e env dag' n
  -- just writing out these 2 was easier than making a more general solution
  makeGraphE1 :: LabelledOpenExp eenv aenv e -> DirectedAcyclicGraph
  makeGraphE1 e = makeGraphE e env dag n
  makeGraphE2
    :: LabelledOpenExp eenv aenv e
    -> LabelledOpenExp fenv aenv f
    -> DirectedAcyclicGraph
  makeGraphE2 e f = makeGraphE e env (makeGraphE f env dag n) n

--like makeGraphE
makeGraphF
  :: LabelledOpenFun env aenv a
  -> [NodeId]
  -> DirectedAcyclicGraph
  -> NodeId
  -> DirectedAcyclicGraph
makeGraphF (Lam  f) = makeGraphF f
makeGraphF (Body b) = makeGraphE b

makeGraphB
  :: PreBoundary LabelledOpenAcc env a
  -> [NodeId]
  -> DirectedAcyclicGraph
  -> NodeId
  -> DirectedAcyclicGraph
makeGraphB (Function f) = makeGraphF f
makeGraphB _            = const const

($:) :: (NodeId, NodeType) -> IM.IntMap NodeType -> IM.IntMap NodeType
($:) (NodeId n, x) = IM.insert n x
($++) :: [(NodeId, NodeType)] -> IM.IntMap NodeType -> IM.IntMap NodeType
($++) xs intmap = foldl' (\im (NodeId n, x) -> IM.insert n x im) intmap xs

-- given a list representing "env", and one representing "a", make a list representing "env'"
applyLHS
  :: LeftHandSide a env env'
  -> [NodeId] -- env
  -> NodeId -- a
  -> [NodeId] -- env'
applyLHS LeftHandSideArray        env a = a : env
applyLHS (LeftHandSideWildcard _) env _ = env
applyLHS (LeftHandSidePair lhs1 lhs2) env a =
  let env' = applyLHS lhs2 env a in applyLHS lhs1 env' a

-- A (pair) variable is apparently not guaranteed to refer to just one bind site, so we return a list
getNodeIds :: [NodeId] -> ArrayVars env a -> [NodeId]
getNodeIds _       ArrayVarsNil                        = []
getNodeIds (n : _) (ArrayVarsArray (ArrayVar ZeroIdx)) = [n]
getNodeIds (_ : ns) (ArrayVarsArray (ArrayVar (SuccIdx idx))) =
  getNodeIds ns $ ArrayVarsArray (ArrayVar idx)
getNodeIds ns (ArrayVarsPair a1 a2) = (getNodeIds ns a1) ++ (getNodeIds ns a2)
getNodeIds [] _ = error "NewFusion/Solver.hs: empty environment"

-- Variables of type 'Array sh e' should only consist of a single NodeId
getNodeId :: [NodeId] -> ArrayVars env (Array sh e) -> NodeId
getNodeId n e =
  (\case
      [x] -> x
      _   -> error "getNodeId failed"
    )
    $ getNodeIds n e







-- for Scans, we ignore the ' variant (which returns both the prefix sums and the final sum as two separate arrays of different dimensions) for now
-- for Scans, 'False' is left-to-right (corresponding to 0 in the ILP)
data NodeType = VarT NodeId | GenerateT | MapT NodeId | ZipWithT NodeId NodeId
              | FoldDimT NodeId | FoldFlatT NodeId | FoldSegDimT NodeId NodeId
              | FoldSegFlatT NodeId NodeId | ScanDimT NodeId Bool
              | ScanFlatT NodeId Bool | PermuteT NodeId NodeId
              | BackpermuteT NodeId | UnfusableT NodeId | StencilT NodeId
              | Stencil2T NodeId NodeId
                deriving Show


-- The intmap contains a minimal description of node (NodeId i) at index i.
-- The list contains the fusion preventing edges.
data DirectedAcyclicGraph = DAG {
  nodes :: IM.IntMap NodeType,
  fpes :: [(NodeId, NodeId)]} deriving Show

data ILPVar = Fusion NodeId   NodeId -- 0 means fused, 1 means not fused (not in the same fusion group)
            | Pi              NodeId -- the number of the fusion group this node is in, used for acyclicity
            | InputShape      NodeId -- -2 represents 'unknown' (backpermute output), -1 represents an even spread across all blocks, X>=0 means each threadblock holds every value along the innermost X dimensions (X=1 represents the current FoldDim approach, and X=0 means each threadblock holds only 1 value)
            | OutputShape     NodeId
            | InputDirection  NodeId -- 0 is ->, 1 is <-, 2 is 'unknown'
            | OutputDirection NodeId deriving (Eq, Ord, Show)





-- The LPM `monad' is a State (LinearProgram variables values) ()
-- We write the LP by using functions like mapM_ to modify the state while discarding the () result
makeILP :: DirectedAcyclicGraph -> LP ILPVar Int
makeILP DAG {..} = execLPM $ do
  let verticals      = concatMap makeVerticals nodes'
  let horizontals    = makeHorizontals verticals
  let verticalVars   = map (uncurry Fusion) verticals
  let horizontalVars = map (uncurry Fusion) horizontals
  let fusionVars     = verticalVars ++ horizontalVars
  let piVars         = map (Pi . fst) nodes'
  let fpeVars = map (uncurry Fusion) (fpes ++ concatMap makeFPEs nodes')

  setDirection Min -- minimise cost function
  setObjective $ linCombination $ map (1, ) fusionVars -- cost function, currently minimising the number of unfused edges

  -- fusion variables
  mapM_ (\x -> varBds x 0 1)    fusionVars

  -- 'pi' variables for acyclicity
  mapM_ (\x -> varBds x 0 maxN) piVars

  -- fpe constraints
  mapM_ (`varEq` 1)             fpeVars

  -- acyclicity contraints
  mapM_ makeAcyclicV            (verticalVars ++ fpeVars)
  mapM_ makeAcyclicH            horizontalVars
  mapM_ makeAcyclicFPE          fpeVars

  -- nodetype-specific constraints:
  -- - input and output shape and direction variables
  mapM_ makeConstraint          nodes'
  -- - rules relating those variables to the fusion variables
  mapM_ fusionShapeV            verticalVars
  mapM_ fusionShapeH            horizontalVars

  -- constrain all variables to be integers
  mapM_ (`setVarKind` IntVar)   (fusionVars ++ piVars ++ fpeVars)
 where
  nodes' :: [(NodeId, NodeType)]
  nodes' = map (first NodeId) (IM.assocs nodes)

  maxN   = (2 *) $ maximum $ map ((\(NodeId n) -> n) . fst) nodes'

  -- the maximum number of innermost dimensions a threadblock may hold, for a fold or scan on multidimensional data
  maxFoldScanDims :: Int
  maxFoldScanDims = 5

  -- All the fusion variables for vertical fusion, (x,y) means that y consumes x
  makeVerticals :: (NodeId, NodeType) -> [(NodeId, NodeId)]
  makeVerticals (x, nodetype) = case nodetype of
    UnfusableT _     -> []
    GenerateT        -> []
    MapT y           -> [(y, x)]
    VarT y           -> [(y, x)]
    ZipWithT y z     -> [(y, x), (z, x)]
    FoldDimT  y      -> [(y, x)]
    FoldFlatT y      -> [(y, x)]
    FoldSegDimT  y _ -> [(y, x)]
    FoldSegFlatT y _ -> [(y, x)]
    ScanDimT     y _ -> [(y, x)]
    ScanFlatT    y _ -> [(y, x)]
    PermuteT     y _ -> [(y, x)] -- can't fuse with the 'target array'
    BackpermuteT y   -> [(y, x)]
    StencilT     _   -> [] -- [(y, x)]
    Stencil2T _ _    -> [] -- [(y, x), (z, x)]

  -- given all the vertical fusion variables (where (x,y) means that the array x could be fused into the computation y),
  -- produce a list of pairs of nodeIds that both consume the same array and could thus be fused horizontally.
  makeHorizontals :: [(NodeId, NodeId)] -> [(NodeId, NodeId)]
  makeHorizontals =
    nub
      . map (\(x, y) -> if x < y then (x, y) else (y, x))
      . concatMap carthesian
      . M.elems
      . M.fromListWith (++)
      . map (second pure)
  carthesian :: [a] -> [(a, a)]
  carthesian []       = []
  carthesian (x : ys) = map (x, ) ys ++ carthesian ys

  makeConstraint :: (NodeId, NodeType) -> LPM ILPVar Int ()
  makeConstraint (n, nodetype) = case nodetype of
    UnfusableT _ -> do
      varBds (OutputDirection n) 0 2
      varGeq (OutputShape n) (-2)
    GenerateT -> do
      varBds (OutputDirection n) 0 2
      varGeq (OutputShape n) (-2)
    MapT _ -> do
      varBds (OutputDirection n) 0 1
      varGeq (OutputShape n) (-2)
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 0
    VarT _ -> do
      varBds (OutputDirection n) 0 1
      varGeq (OutputShape n) (-2)
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 0
    ZipWithT _ _ -> do
      varBds (OutputDirection n) 0 2
      varGeq (OutputShape n) (-2)
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 0
    FoldDimT _ -> do
      varBds (OutputDirection n) 0 2
      varBds (OutputShape n)     0 maxFoldScanDims
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 1
    FoldFlatT _ -> do
      varBds (InputDirection n) 0 2 -- the output of a FoldFlat is just one element, so no variables needed
      varEq (InputShape n) (-1)
    FoldSegDimT _ _ -> do
      varBds (OutputDirection n) 0 2
      varBds (OutputShape n)     0 maxFoldScanDims
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 1
    FoldSegFlatT _ _ -> do
      varBds (InputDirection n) 0 2 -- the output of a FoldFlat is just one element, so no variables needed
      varEq (InputShape n) (-1)
    ScanDimT _ b -> do
      varEq (OutputDirection n) (fromEnum b)
      varBds (OutputShape n) 1 maxFoldScanDims
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 0
    ScanFlatT _ b -> do
      varEq (InputDirection n) (fromEnum b)
      varEq (InputShape n)     (-1)
      equalTo
        (linCombination [(-1, OutputDirection n), (1, InputDirection n)])
        0
      equalTo (linCombination [(-1, OutputShape n), (1, InputShape n)]) 0
    PermuteT _ _ -> do -- TODO fix backpermute . permute by adding a -1 direction
      varBds (InputDirection n) 0 2 -- can't fuse the output of a permute, so no variable needed
      varGeq (InputShape n) (-2)
    BackpermuteT _ -> do
      varBds (OutputDirection n) 0 2 -- the output can be any shape, but the input has to be every shape
      varGeq (OutputShape n) (-2)
      varEq (InputDirection n) 2
      varEq (InputShape n)     (-2)
    StencilT _ -> do
      varBds (OutputDirection n) 0 2 -- for now, stencils don't fuse with their inputs so no input variables needed
      varGeq (OutputShape n) (-2)
    Stencil2T _ _ -> do
      varBds (OutputDirection n) 0 2 -- for now, stencils don't fuse with their inputs so no input variables needed
      varGeq (OutputShape n) (-2)

  -- generate the constraints belonging to a vertical fusion: if fused, the input and output have to match
  fusionShapeV, fusionShapeH :: ILPVar -> LPM ILPVar Int ()
  fusionShapeV (Fusion x y) = do
    leqTo
      (linCombination
        [(-1, OutputDirection x), (1, InputDirection y), (-2, Fusion x y)]
      )
      0 -- Because the direction is between 0 and 2, this ensures that if fused the directions are equal without imposing restrictions if not fused
    leqTo
      (linCombination
        [(1, OutputDirection x), (-1, InputDirection y), (-2, Fusion x y)]
      )
      0
    leqTo
      (linCombination
        [(-1, OutputShape x), (1, InputShape y), (-maxFoldScanDims, Fusion x y)]
      )
      0
    leqTo
      (linCombination
        [(1, OutputShape x), (-1, InputShape y), (-maxFoldScanDims, Fusion x y)]
      )
      0
  fusionShapeV _ = ilpError

  -- generate the constraints belonging to a horizontal fusion: if fused, the inputs have to match
  fusionShapeH (Fusion x y) = do
    leqTo
      (linCombination
        [(-1, InputDirection x), (1, InputDirection y), (-2, Fusion x y)]
      )
      0 -- Because the direction is between 0 and 2, this ensures that if fused the directions are equal without imposing restrictions if not fused
    leqTo
      (linCombination
        [(1, InputDirection x), (-1, InputDirection y), (-2, Fusion x y)]
      )
      0
    leqTo
      (linCombination
        [(-1, InputShape x), (1, InputShape y), (-maxFoldScanDims, Fusion x y)]
      )
      0
    leqTo
      (linCombination
        [(1, InputShape x), (-1, InputShape y), (-maxFoldScanDims, Fusion x y)]
      )
      0
  fusionShapeH _ = ilpError


  makeAcyclicV, makeAcyclicH, makeAcyclicFPE :: ILPVar -> LPM ILPVar Int ()
  makeAcyclicV (Fusion x y) = do
    leqTo (linCombination [(1, Fusion x y), (-1, Pi y), (1, Pi x)])     0 -- f_{x,y} ≤ pi_y − pi_x   ==> precedence-preserving
    leqTo (linCombination [(-maxN, Fusion x y), (1, Pi y), (-1, Pi x)]) 0 -- pi_y − pi_x ≤ N*f_{x,y} ==> guarantees that the pi's are equal if fused
  makeAcyclicV _ = ilpError

  makeAcyclicH (Fusion x y) = do
    leqTo (linCombination [(-maxN, Fusion x y), (-1, Pi y), (1, Pi x)]) 0 -- −N*f_{i,j} ≤ pi_y - pi_x
    leqTo (linCombination [(-maxN, Fusion x y), (1, Pi y), (-1, Pi x)]) 0 -- pi_y − pi_x ≤ N*f_{x,y} ==> guarantees that the pi's are equal if fused
  makeAcyclicH _ = ilpError

  makeAcyclicFPE (Fusion x y) =
    geqTo (linCombination [(1, Pi y), (-1, Pi x)]) 1 -- strictly bigger than 0 in integers
  makeAcyclicFPE _ = ilpError

  makeFPEs :: (NodeId, NodeType) -> [(NodeId, NodeId)]
  makeFPEs (n, nodetype) = case nodetype of
    VarT _           -> []
    MapT _           -> []
    GenerateT        -> []
    ZipWithT _ _     -> []
    FoldDimT  _      -> []
    FoldFlatT _      -> []
    FoldSegDimT  _ s -> [(s, n)]
    FoldSegFlatT _ s -> [(s, n)]
    ScanDimT     _ _ -> []
    ScanFlatT    _ _ -> []
    PermuteT     _ m -> [(m, n)]
    BackpermuteT _   -> []
    UnfusableT   m   -> [(m, n)]
    StencilT     m   -> [(m, n)]
    Stencil2T m o    -> [(m, n), (o, n)]


  ilpError =
    error
      "A function expected '(Fusion x y)' but got something else in NewFusion/Solver.hs"


callGLPKTest :: LP ILPVar Int -> IO ()
callGLPKTest lp = do
  --print "ilp:"
  --print lp
  --print "using simplexDefaults:"
  --res1 <- glpSolveVars opt1 lp
  --print res1
  print "using mipDefaults:"
  res2 <- glpSolveVars opt2 lp
  print res2
  where
  --opt1 = simplexDefaults
        opt2 = mipDefaults

-- the doubles in the return type are always whole numbers, but glpk-hs just always returns this
callGLPK :: LP ILPVar Int -> IO (M.Map ILPVar Double)
callGLPK lp = do
  (_, x) <- glpSolveVars mipDefaults lp
  let Just (_, m) = x -- panics if something went wrong
  return m

groupNodes :: M.Map ILPVar Double -> [[NodeId]]
groupNodes =
  map (map ((\(Pi n) -> n) . fst))
    . groupBy ((==) @Int `on` (round . snd))
    . sortBy (compare `on` snd)
    . filter (isPi . fst)
    . M.assocs
 where
  isPi (Pi _) = True
  isPi _      = False
