{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

data SomeConstraint = SomeConstraint { getSomeConstraint :: forall repr. GenCs repr => ConstraintE repr }

type Constraints = [SomeConstraint]

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

data ConstraintGenResults =
  ConstraintGenResults
    { cgUsed :: UsedIds
    , cgConstraints :: Constraints
    }

instance Semigroup ConstraintGenResults where
  x <> y =
    ConstraintGenResults
      { cgUsed = cgUsed x <> cgUsed y
      , cgConstraints = cgConstraints x <> cgConstraints y
      }

instance Monoid ConstraintGenResults where
  mempty =
    ConstraintGenResults
      { cgUsed = mempty
      , cgConstraints = mempty
      }

newtype IdTracker a = IdTracker { runIdTracker :: Writer UsedIds () }
-- newtype PprExpr a = PprExpr

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

newtype ConstraintGen a = ConstraintGen (Writer Constraints a)
  deriving (Functor, Applicative, Monad, MonadWriter Constraints)

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
  idTrackerValue (v, x) = tellVars [v] <> retag (idTrackerValue x)

instance IdTrackerValue Var where
  idTrackerValue v = tellVars [v]

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

  setValue = error "IdTracker: setValue" --idTrackerSetValue
  x `union` y = x <> y
  x `unionSingle` y = x <> retag y
  empty = idTrackerAny
  setCompr f p z = retag (f idTrackerAny) <> retag (p idTrackerAny) <> retag z

instance LatticeExpr IdTracker where
  type LatticeCt IdTracker = Unconstrained
  lub xs = retag xs

idTrackerOnConstraints :: Constraints -> UsedIds
idTrackerOnConstraints = mconcat . map (\(SomeConstraint x) -> go x)
  where
    go :: ConstraintE IdTracker -> UsedIds
    go (IdTracker x :=: IdTracker y) = execWriter x <> execWriter y

execIdTracker :: ConstraintGen a -> UsedIds
execIdTracker (ConstraintGen g) = idTrackerOnConstraints $ execWriter g

execConstraintGen :: ConstraintGen () -> ConstraintGenResults
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

handleDeclarator :: CDeclarator NodeId -> ConstraintGen ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [SomeConstraint (value (C_Exit n) :=: unionSingle (value (C_Entry n)) (value (Var hash, SensAtom Secret)))]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [SomeConstraint (value (C_Exit n) :=: unionSingle (value (C_Entry n)) (value (Var hash, SensAtom Public)))]

handleDeclarator e = nop e

handleCompoundItem :: CCompoundBlockItem NodeId -> ConstraintGen ()
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

handleExpr :: CExpression NodeId -> ConstraintGen ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  tell [ SomeConstraint (value (E_Family (annotation e0)) :=: union (value (E_Family (annotation cv)))
                                                       (value (E_Family (annotation e)))) ]

  handleExpr cv
  tell [ SomeConstraint (value (C_Exit n) :=: ite (in_ (value (Var x, SensAtom Public)) (value (C_Entry n)))
                                    (unionSingle (value (C_Entry n)) (value (Var x, (SensT (annotation e)))))
                                    (value (C_Entry n)))
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) =
  tell [ SomeConstraint (value (E_Family (annotation e)) :=: unionSingle empty (value (Var x))) ]

handleExpr expr = do
  nop expr
  let theChildren = children expr

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]
    sameNode c expr
    tell [ SomeConstraint (value (E_Family (annotation c)) :=: value (E_Family (annotation expr))) ]
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
    exprNodeId = annotation expr

handleStmt :: CStatement NodeId -> ConstraintGen ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ SomeConstraint (value (C_Entry (annotation cond)) :=: value (C_Entry l)) ]

  tell $
      [entryConstraint t
      ,SomeConstraint (
          let maybeUnion x g =
                case f_maybe of
                  Nothing -> value x
                  Just f -> union (value x) (value (g (annotation f)))
          in
          value (C_Exit l) :=: union (value (C_Entry l))
                 (ite (value (SensT l) `equal` value (SensAtom Secret))
                   (maybeUnion (S_Family l m) (S_Family l))
                   (maybeUnion (C_Exit m) C_Exit)))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]


  handleStmt t

  tell [SomeConstraint (value (E_Family (annotation e0)) :=: value (E_Family (annotation cond)))]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    entryConstraint x = SomeConstraint (value (C_Entry (annotation x)) :=: value (C_Entry l))

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
nop :: (Annotated f) => f NodeId -> ConstraintGen ()
nop e =
  tell
    [ SomeConstraint (value (C_Exit (annotation e)) :=: value (C_Entry (annotation e))) ]

connectList :: (Annotated f) => [f NodeId] -> ConstraintGen ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen ()
connect x y =
  tell
    [ SomeConstraint (value (C_Entry (annotation y)) :=: value (C_Exit (annotation x))) ]

-- | Combine two nodes, to behave as one
sameNode :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen ()
sameNode x y =
  tell
    [ SomeConstraint (value (C_Entry (annotation x)) :=: value (C_Entry (annotation y)))
    , SomeConstraint (value (C_Exit  (annotation x)) :=: value (C_Exit  (annotation y)))
    ]

-- TODO: Connect to following nodes
handleFunDef :: CFunctionDef NodeId -> ConstraintGen ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ SomeConstraint (value (C_Exit (annotation e)) :=: empty)
    , SomeConstraint (value (C_Entry (annotation stmt)) :=: value (C_Exit (annotation e)))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: CExternalDeclaration NodeId -> ConstraintGen ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (CTranslationUnit NodeId, NodeId) -> ConstraintGen ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

