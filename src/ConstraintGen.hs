{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedLists #-}

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

newtype Var = Var { getVar :: Int }
  deriving (Show, Eq, Ord, Data)

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Ord, Data)

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

type Constraints repr = [ConstraintE repr]

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
      , nodeIdsUsed = nodeIdsUsed x <> nodeIdsUsed x
      }

instance Monoid UsedIds where
  mempty = UsedIds mempty mempty mempty mempty

data ConstraintGenResults repr =
  ConstraintGenResults
    { cgUsed :: UsedIds
    , cgConstraints :: Constraints repr
    }

instance Semigroup (ConstraintGenResults repr) where
  x <> y =
    ConstraintGenResults
      { cgUsed = cgUsed x <> cgUsed y
      , cgConstraints = cgConstraints x <> cgConstraints y
      }

instance Monoid (ConstraintGenResults repr) where
  mempty =
    ConstraintGenResults
      { cgUsed = mempty
      , cgConstraints = mempty
      }

newtype IdTracker a = IdTracker { runIdTracker :: Writer UsedIds () }

instance Semigroup (IdTracker a) where
  IdTracker x <> IdTracker y = IdTracker (x >> y)

tellTNodes :: Set NodeId -> IdTracker a
tellTNodes ns = IdTracker $ do
  tell mempty { tNodesUsed = ns }
  runIdTracker $ tellNodeIds ns

tellSPairs :: Set (NodeId, NodeId) -> IdTracker a
tellSPairs sp = IdTracker $ do
  tell mempty { sPairsUsed = sp }
  runIdTracker $ tellNodeIds (Set.map fst sp)
  runIdTracker $ tellNodeIds (Set.map snd sp)

tellVars :: Set Var -> IdTracker a
tellVars vs = IdTracker $ tell mempty { varsUsed = vs }

tellNodeIds :: Set NodeId -> IdTracker a
tellNodeIds ns = IdTracker $ tell mempty { nodeIdsUsed = ns }

newtype ConstraintGen repr a = ConstraintGen (Writer (Constraints repr) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints repr))

type GenCs repr = (Expr repr, ValueCt repr Var, EqualCt repr SensExpr, SetCt repr AnalysisSetFamily, SetElemCt repr Var, ValueCt repr (AnalysisSetFamily Var), SetElemCt repr (Var, SensExpr), LatticeCt repr SensExpr, ValueCt repr (Var, SensExpr), ValueCt repr (AnalysisSetFamily (Var, SensExpr)), ValueCt repr SensExpr)
  :: Constraint

-- tellUsed :: UsedIds -> ConstraintGen repr ()
-- tellUsed used = tell (mempty { cgUsed = used })

-- tellTNodesUsed :: [NodeId] -> ConstraintGen repr ()
-- tellTNodesUsed ns = tellUsed (mempty { tNodesUsed = ns })

-- tellSPairsUsed :: [(NodeId, NodeId)]

class IdTrackerValue a where
  idTrackerValue :: a -> IdTracker a

idTrackerAny :: IdTracker a
idTrackerAny = IdTracker $ return ()

retag :: IdTracker a -> IdTracker b
retag (IdTracker x) = IdTracker x

instance IdTrackerValue (AnalysisSetFamily a) where
  idTrackerValue (C_Entry n) = tellNodeIds [n]
  idTrackerValue (C_Exit n)  = tellNodeIds [n]
  idTrackerValue (S_Family m n) = tellSPairs [(m, n)]
  idTrackerValue (B_Family n) = tellNodeIds [n]
  idTrackerValue (E_Family n) = tellNodeIds [n]

instance IdTrackerValue SensExpr where
  idTrackerValue (SensAtom _) = idTrackerAny
  idTrackerValue (SensT n) = tellTNodes [n]

instance IdTrackerValue (Var, SensExpr) where
  idTrackerValue _ = idTrackerAny

instance IdTrackerValue Var where
  idTrackerValue _ = idTrackerAny

instance Value IdTracker where
  type ValueCt IdTracker = IdTrackerValue
  value = idTrackerValue

instance BoolExpr IdTracker where
  type EqualCt IdTracker = ((~) SensExpr)

  x `in_` xs = retag (x <> retag xs)
  x ^&&^ y = x <> y
  true = idTrackerAny
  false = idTrackerAny
  x `equal` y = retag (x <> y)
  ite c t f = retag (c <> retag t <> retag f)

class IdTrackerSet set where
  idTrackerSetValue :: set a -> IdTracker (set a)

instance IdTrackerSet AnalysisSetFamily where
  idTrackerSetValue = value

instance SetExpr IdTracker where
  type SetCt IdTracker = IdTrackerSet
  type SetElemCt IdTracker = Unconstrained

  setValue = idTrackerSetValue
  x `union` y = x <> y
  x `unionSingle` y = x <> retag y
  empty = idTrackerAny
  setCompr f p z = retag (f idTrackerAny) <> retag (p idTrackerAny) <> retag z

instance LatticeExpr IdTracker where
  type LatticeCt IdTracker = Unconstrained
  lub xs = retag xs

execIdTracker :: ConstraintGen IdTracker a -> UsedIds
execIdTracker (ConstraintGen g) = mconcat $ map go $ execWriter g
  where
    go :: ConstraintE IdTracker -> UsedIds
    go (IdTracker x :=: IdTracker y) = execWriter x <> execWriter y

execConstraintGen :: GenCs repr => (forall r. GenCs r => ConstraintGen r a) -> ConstraintGenResults repr
execConstraintGen cg@(ConstraintGen g) =
  ConstraintGenResults
    { cgConstraints = execWriter g
    , cgUsed = execIdTracker cg
    }

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: (GenCs repr) => CDeclarator NodeId -> ConstraintGen repr ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [setValue (C_Exit n) :=: unionSingle (setValue (C_Entry n)) (value (Var hash, SensAtom Secret))]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [setValue (C_Exit n) :=: unionSingle (setValue (C_Entry n)) (value (Var hash, (SensAtom Public)))]

handleDeclarator e = nop e

handleCompoundItem :: (GenCs repr) => CCompoundBlockItem NodeId -> ConstraintGen repr ()
handleCompoundItem (CBlockDecl e@(CDecl _ [] _)) = nop e
handleCompoundItem (CBlockDecl e@(CDecl declSpec xs _)) = do
    -- nop e

    mapM_ (sameNode e) declSpec

    -- mapM_ (sameNode e) $ catMaybes $ map (\(z, _, _) -> z) xs

    -- case catMaybes $ map (\(z, _, _) -> z) xs of
    --   [] -> pure ()
    --   xs'@(x:_) -> do
    --     e `connect` x
    --     connectList xs'

    mapM_ go xs
  where
    go (Just declr, _, _) = sameNode e declr *> handleDeclarator declr
    go _ = pure ()
-- handleCompoundItem (CBlockDecl {}) = pure ()
handleCompoundItem (CBlockDecl e) = nop e
handleCompoundItem (CBlockStmt stmt) = handleStmt stmt -- pure ()
handleCompoundItem (CNestedFunDef funDef) = handleFunDef funDef

handleExpr :: (GenCs repr) => CExpression NodeId -> ConstraintGen repr ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  tell [ setValue (E_Family (annotation e0)) :=: union (value (E_Family (annotation cv)))
                                                       (value (E_Family (annotation e))) ]

  handleExpr cv
  tell [ setValue (C_Exit n) :=: ite (in_ (value (Var x, SensAtom Public)) (value (C_Entry n)))
                                    (unionSingle (value (C_Entry n)) (value (Var x, (SensT (annotation e)))))
                                    (value (C_Entry n))
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) =
  tell [ setValue (E_Family (annotation e)) :=: unionSingle empty (value (Var x)) ]

handleExpr expr = do
  nop expr
  let theChildren = children expr

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]
    sameNode c expr
    tell [ setValue (E_Family (annotation c)) :=: value (E_Family (annotation expr)) ]
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
    exprNodeId = annotation expr

handleStmt :: (GenCs repr) => CStatement NodeId -> ConstraintGen repr ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ setValue (C_Entry (annotation cond)) :=: value (C_Entry l) ]

  tell go

  handleStmt t

  tell [setValue (E_Family (annotation e0)) :=: value (E_Family (annotation cond))]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,setValue (C_Exit l) :=: union (value (C_Entry l))
                             (ite (value (SensT l) `equal` value (SensAtom Secret))
                               (maybeUnion (S_Family l m) (S_Family l))
                               (maybeUnion (C_Exit m) C_Exit))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = setValue (C_Entry (annotation x)) :=: value (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> value x
        Just f -> union (value x) (value (g (annotation f)))

    p = annotation cond
    m = annotation t

handleStmt e@(CCompound _ items _) = do
  nop e

  case items of
    [] -> pure ()
    (firstItem:_) -> --tell [ c_entry (annotation firstItem) :=: c_exit (annotation e) ]
      e `connect` firstItem

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
nop :: (GenCs repr, Annotated f) => f NodeId -> ConstraintGen repr ()
nop e =
  tell
    [ setValue (C_Exit (annotation e)) :=: value (C_Entry (annotation e)) ]

connectList :: (GenCs repr, Annotated f) => [f NodeId] -> ConstraintGen repr ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (GenCs repr, Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen repr ()
connect x y =
  tell
    [ setValue (C_Entry (annotation y)) :=: value (C_Exit (annotation x)) ]

-- | Combine two nodes, to behave as one
sameNode :: (GenCs repr, Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen repr ()
sameNode x y =
  tell
    [ setValue (C_Entry (annotation x)) :=: value (C_Entry (annotation y))
    , setValue (C_Exit  (annotation x)) :=: value (C_Exit  (annotation y))
    ]

-- TODO: Connect to following nodes
handleFunDef :: (GenCs repr) => CFunctionDef NodeId -> ConstraintGen repr ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ setValue (C_Exit (annotation e)) :=: empty
    , setValue (C_Entry (annotation stmt)) :=: value (C_Exit (annotation e))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: (GenCs repr) => CExternalDeclaration NodeId -> ConstraintGen repr ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (GenCs repr) => (CTranslationUnit NodeId, NodeId) -> ConstraintGen repr ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

