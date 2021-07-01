{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module ConstraintGen where

import           Language.C
import           Language.C.Data.Ident

import           Data.Data

import           Data.Constraint

import           Control.Monad.Writer
import           Data.Generics.Uniplate.Data

import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Maybe

import           SetExpr
import           Ppr

newtype Var = Var { getVar :: Int }
  deriving (Show, Eq, Ord, Data)

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Ord, Data)

instance Ppr NodeId where
  ppr (NodeId n) = 'n' : show n

data Sensitivity = Public | Secret
  deriving (Show, Eq)

data SensExpr where
  SensAtom :: Sensitivity -> SensExpr
  SensT :: NodeId -> SensExpr

-- | The set family for this analysis
data AnalysisSetFamily a where
  C_Entry :: NodeId -> AnalysisSetFamily (Var, SensExpr)
  C_Exit :: NodeId -> AnalysisSetFamily (Var, SensExpr)

  S_Family :: NodeId -> NodeId -> AnalysisSetFamily (Var, SensExpr)
  B_Family :: NodeId -> AnalysisSetFamily Var
  E_Family :: NodeId -> AnalysisSetFamily Var

type AnalysisConstraint r = ConstraintE r Var SensExpr AnalysisSetFamily

type Constraints r = [AnalysisConstraint r]

type AnalysisExpr r a = Expr r Var SensExpr AnalysisSetFamily a

data UsedIds =
  UsedIds
    { tNodesUsed :: Set NodeId
    , sPairsUsed :: Set (NodeId, NodeId)
    , varsUsed :: Set Var
    , nodeIdsUsed :: Set NodeId
    }

instance Semigroup UsedIds where
  x <> y =
    UsedIds
      { tNodesUsed  = tNodesUsed  x <> tNodesUsed  y
      , sPairsUsed  = sPairsUsed  x <> sPairsUsed  y
      , varsUsed    = varsUsed    x <> varsUsed    y
      , nodeIdsUsed = nodeIdsUsed x <> nodeIdsUsed y
      }

instance Monoid UsedIds where
  mempty = UsedIds mempty mempty mempty mempty

tellTNodes :: Set NodeId -> Writer UsedIds ()
tellTNodes ns = do
  tell mempty { tNodesUsed = ns }
  tellNodeIds ns

tellSPairs :: Set (NodeId, NodeId) -> Writer UsedIds ()
tellSPairs sp = do
  tell mempty { sPairsUsed = sp }
  tellNodeIds (Set.map fst sp)
  tellNodeIds (Set.map snd sp)

tellVars :: Set Var -> Writer UsedIds ()
tellVars vs = tell mempty { varsUsed = vs }

tellNodeIds :: Set NodeId -> Writer UsedIds ()
tellNodeIds ns = tell mempty { nodeIdsUsed = ns }

getUsedIds_constraint :: AnalysisConstraint r -> Writer UsedIds ()
getUsedIds_constraint ct =
  case ct of
    x :=: y -> goE x >> goE y
    x :>: y -> goE x >> goE y
  where
    goSF :: AnalysisSetFamily a -> Writer UsedIds ()
    goSF (C_Entry n) = tellNodeIds [n]
    goSF (C_Exit n)  = tellNodeIds [n]
    goSF (S_Family m n) = tellSPairs [(m, n)]
    goSF (B_Family n) = tellNodeIds [n]
    goSF (E_Family n) = tellNodeIds [n]

    goE :: AnalysisExpr r a -> Writer UsedIds ()
    goE (SetFamily sf) = goSF sf
    goE (BaseVal v) = tellVars [v]
    goE (MonoidVal (SensT n)) = tellTNodes [n]
    goE (MonoidVal (SensAtom _)) = return ()
    goE (BoolVal _) = return ()

    goE (VarRepr _) = return ()

    goE (Pair x y) = goE x >> goE y
    goE (Fst p) = goE p
    goE (Snd p) = goE p

    goE (In x xs) = goE x >> goE xs
    goE (And x y) = goE x >> goE y
    goE (BaseEqual x y) = goE x >> goE y
    goE (MonoidEqual x y) = goE x >> goE y
    goE (Ite c t f) = goE c >> goE t >> goE f

    goE (Union xs ys) = goE xs >> goE ys
    goE (UnionSingle xs x) = goE xs >> goE x
    goE Empty = return ()

    goE (SetCompr {}) = return () -----
    goE (Lub xs) = goE xs

getUsedIds' :: AnalysisConstraint r -> UsedIds
getUsedIds' = execWriter . getUsedIds_constraint

getUsedIds :: Constraints r -> UsedIds
getUsedIds = execWriter . mapM getUsedIds_constraint

type AnalysisCt r = (ElemVal r, ElemRepr r (Var, SensExpr), ElemRepr r Var)

newtype ConstraintGen r a = ConstraintGen (Writer (Constraints r) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints r))

execConstraintGen :: AnalysisCt r => ConstraintGen r () -> Constraints r
execConstraintGen (ConstraintGen g) = execWriter g

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: AnalysisCt r => CDeclarator NodeId -> ConstraintGen r ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      -- mapM_ (sameNode e) attrs
      mapM_ (connect e) attrs

      tell [(SetFamily (C_Exit n) :=: UnionSingle (SetFamily (C_Entry n)) (uncurry Pair (value $ Var hash, value $ SensAtom Secret)))]

  | otherwise = do
      -- mapM_ (sameNode e) attrs
      mapM_ (connect e) attrs
      tell [(SetFamily (C_Exit n) :=: UnionSingle (SetFamily (C_Entry n)) (uncurry Pair (value $ Var hash, value $ SensAtom Public)))]

handleDeclarator e = nop e

handleCompoundItem :: AnalysisCt r => CCompoundBlockItem NodeId -> ConstraintGen r ()
handleCompoundItem e@(CBlockDecl (CDecl _ [] _)) = nop e
handleCompoundItem e@(CBlockDecl (CDecl declSpec xs _)) = do
    nop e

    -- sameNode e0 e

    mapM_ nop declSpec

    -- mapM_ (sameNode e) declSpec
    mapM_ (connect e) declSpec

    -- mapM_ (sameNode e) $ catMaybes $ map (\(z, _, _) -> z) xs

    -- case catMaybes $ map (\(z, _, _) -> z) xs of
    --   [] -> pure ()
    --   xs'@(x:_) -> do
    --     e `connect` x
    --     connectList xs'

    mapM_ go xs
  where
    -- go (Just declr, _, _) = sameNode e declr *> handleDeclarator declr
    go (Just declr, _, _) = nop declr *> connect e declr *> handleDeclarator declr
    go _ = pure ()
-- handleCompoundItem (CBlockDecl {}) = pure ()
handleCompoundItem (CBlockDecl e) = nop e
handleCompoundItem (CBlockStmt stmt) = handleStmt stmt -- pure ()
handleCompoundItem (CNestedFunDef funDef) = handleFunDef funDef

handleExpr :: AnalysisCt r => CExpression NodeId -> ConstraintGen r ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  -- sameNode e e0
  -- sameNode cv e0

  -- connect e0 e
  connect e0 cv

  -- sameNode e0 e
  -- sameNode e0 cv

  -- tell [ SetFamily (C_Entry (annotation e)) :=: SetFamily (C_Entry (annotation e0)) ]
  -- tell [ SetFamily (C_Entry (annotation cv)) :=: SetFamily (C_Entry (annotation e0)) ]

  tell [ (SetFamily (E_Family (annotation e0)) :=: Union (value (E_Family (annotation cv)))
                                                       (value (E_Family (annotation e)))) ]

  handleExpr cv
  tell [ (SetFamily (C_Exit n) :=: Ite (In (value (Var x, SensAtom Public)) (SetFamily (C_Entry n)))
                                    (UnionSingle (value (C_Entry n)) (uncurry Pair (value $ Var x, value $ SensT (annotation e))))
                                    (value (C_Entry n)))
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) = do
  nop e
  tell [ (SetFamily (E_Family (annotation e)) :=: UnionSingle Empty (value (Var x)))
       ]

handleExpr expr = do
  nop expr
  let theChildren = children expr

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]

    -- sameNode c expr
    sameNode expr c

    tell [ (SetFamily (E_Family (annotation c)) :=: value (E_Family (annotation expr))) ]
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
    exprNodeId = annotation expr

handleStmt :: AnalysisCt r => CStatement NodeId -> ConstraintGen r ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ (SetFamily (C_Entry (annotation cond)) :=: value (C_Entry l)) ]

  tell $
      [entryConstraint t
      ,(
          let maybeUnion x g =
                case f_maybe of
                  Nothing -> SetFamily x
                  Just f -> Union (value x) (value (g (annotation f)))
          in
          value (C_Exit l) :=: Union (value (C_Entry l))
                 (Ite (MonoidVal (SensT l) `MonoidEqual` value (SensAtom Secret))
                   (maybeUnion (S_Family l m) (S_Family l))
                   (maybeUnion (C_Exit m) C_Exit)))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]


  handleStmt t

  tell [(SetFamily (E_Family (annotation e0)) :=: value (E_Family (annotation cond)))]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    entryConstraint x = (SetFamily (C_Entry (annotation x)) :=: value (C_Entry l))

    p = annotation cond
    m = annotation t

handleStmt e@(CCompound _ items _) = do
  -- nop e

  case items of
    [] -> pure ()
    (firstItem:_) -> do --tell [ c_entry (annotation firstItem) :=: c_exit (annotation e) ]
      e `connect` firstItem
      -- tell [ SetFamily (C_Exit (annotation e)) :=: SetFamily (C_Exit (annotation (last items))) ]
      tell [ SetFamily (C_Exit (annotation (last items))) :>: SetFamily (C_Exit (annotation e)) ]

  connectList items
  mapM_ handleCompoundItem items

handleStmt e = do --pure () --mapM_ handleStmt $ drop 1 $ universe e -- pure ()
  nop e

  case children e of
    [] -> pure ()
    cs@(c:_) -> do
      e `connect` c

      connectList cs

      mapM_ handleStmt cs

-- | Generate C_Exit(n) = C_Entry(n) constraint for given node
nop :: (Annotated f) => f NodeId -> ConstraintGen r ()
nop e =
  tell
    [ (SetFamily (C_Exit (annotation e)) :=: value (C_Entry (annotation e))) ]

connectList :: (Annotated f) => [f NodeId] -> ConstraintGen r ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen r ()
connect x y =
  tell
    [ (SetFamily (C_Entry (annotation y)) :=: value (C_Exit (annotation x))) ]

-- | Combine two nodes, to behave as one
sameNode :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen r ()
sameNode x y = do
  return ()
  -- nop y
  -- x `connect` y

  -- tell
  --   [ SetFamily (C_Entry (annotation y)) :>: value (C_Entry (annotation x))
  --   , SetFamily (C_Exit  (annotation y)) :>: value (C_Exit  (annotation x))
  --   ]

  -- tell
  --   [ (SetFamily (C_Entry (annotation x)) :=: value (C_Entry (annotation y)))
  --   , (SetFamily (C_Exit  (annotation x)) :=: value (C_Exit  (annotation y)))
  --   ]

-- TODO: Connect to following nodes
handleFunDef :: AnalysisCt r => CFunctionDef NodeId -> ConstraintGen r ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ (SetFamily (C_Exit (annotation e)) :=: Empty)
    , (SetFamily (C_Entry (annotation stmt)) :=: value (C_Exit (annotation e)))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: AnalysisCt r => CExternalDeclaration NodeId -> ConstraintGen r ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: AnalysisCt r => (CTranslationUnit NodeId, NodeId) -> ConstraintGen r ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

