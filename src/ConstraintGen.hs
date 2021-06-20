{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module ConstraintGen where

import           Language.C
import           Language.C.Data.Ident

import           Data.Data

import           Control.Monad.Writer
import           Data.Generics.Uniplate.Data

import           Data.Maybe

import           SetExpr

newtype Var = Var { getVar :: Int }
  deriving (Show, Eq, Ord, Data)

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Ord, Data)

data Sensitivity = Public | Secret
  deriving (Show, Eq)

data SensFamily a where
  SensT :: NodeId -> SensFamily Sensitivity

data SensExpr' where
  SensAtom' :: Sensitivity -> SensExpr'
  SensFamily' :: SensFamily a -> SensExpr'

-- pattern SensAtom :: ReprC AnalysisSetFamily SensExpr => Sensitivity -> SensExpr
-- pattern SensAtom   s  = LatticeVal' (SensAtom' s)
-- pattern SensFamily sf = LatticeVal' (SensFamily' sf)

sensAtom s = LatticeVal' (convert (SensAtom' s))
sensFamily sf = LatticeVal' (convert (SensFamily' sf))

type SensExpr = LatticeExpr AnalysisSetFamily SensExpr'

-- | The set family for this analysis
data AnalysisSetFamily a where
  C_Entry :: NodeId -> AnalysisSetFamily (Var, SensExpr)
  C_Exit :: NodeId -> AnalysisSetFamily (Var, SensExpr)

  S :: NodeId -> NodeId -> AnalysisSetFamily (Var, SensExpr)
  B :: NodeId -> AnalysisSetFamily Var

class AnalysisSfExpr f where
  c_entry :: NodeId -> f (Var, SensExpr)
  c_exit  :: NodeId -> f (Var, SensExpr)

  s_family :: NodeId -> NodeId -> f (Var, SensExpr)
  b_family :: NodeId -> f Var

instance AnalysisSfExpr AnalysisSetFamily where
  c_entry = C_Entry
  c_exit = C_Exit
  s_family n = S n
  b_family = B

instance AnalysisSfExpr (SetExpr AnalysisSetFamily) where
  c_entry = SetFamily . c_entry
  c_exit = SetFamily . c_exit
  s_family n = SetFamily . s_family n
  b_family = SetFamily . b_family

type Constraints c = [SomeConstraint c AnalysisSetFamily]


newtype ConstraintGen c a = ConstraintGen (Writer (Constraints c) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints c))


execConstraintGen :: ConstraintGen c a -> Constraints c
execConstraintGen (ConstraintGen g) = execWriter g

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: c (Var, SensExpr) => CDeclarator NodeId -> ConstraintGen c ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [c_exit n .=. SetUnionSingle (c_entry n) (Var hash, sensAtom Secret)]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [c_exit n .=. SetUnionSingle (c_entry n) (Var hash, (sensAtom Public))]

handleDeclarator e = nop e

handleCompoundItem :: c (Var, SensExpr) => CCompoundBlockItem NodeId -> ConstraintGen c ()
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

handleExpr :: c (Var, SensExpr) => CExpression NodeId -> ConstraintGen c ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  handleExpr cv
  tell [ c_exit n .=. ite (In' (Var x, sensAtom Public) (c_entry n))
                                    (SetUnionSingle (c_entry n) (Var x, (sensFamily (SensT (annotation e)))))
                                    (c_entry n)
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) = return ()

handleExpr expr = do
  nop expr
  let theChildren = children expr

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]
    sameNode c expr
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
    exprNodeId = annotation expr

handleStmt :: c (Var, SensExpr) => CStatement NodeId -> ConstraintGen c ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ c_entry (annotation cond) .=. SetFamily (c_entry l) ]

  tell go

  handleStmt t

  -- tell [atom_e (annotation e0) :=: atom_e (annotation cond)]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,c_exit l .=. SetUnion (c_entry l)
                             (ite (sensFamily (SensT l) `LatticeEqual` sensAtom Secret)
                               (maybeUnion (s_family l m) (s_family l))
                               (maybeUnion (c_exit m) c_exit))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = c_entry (annotation x) .=. SetFamily (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> x
        Just f -> SetUnion x (g (annotation f))

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
nop :: (c (Var, SensExpr), Annotated f) => f NodeId -> ConstraintGen c ()
nop e =
  tell
    [ c_exit (annotation e) .=. SetFamily (C_Entry (annotation e)) ]

connectList :: (c (Var, SensExpr), Annotated f) => [f NodeId] -> ConstraintGen c ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (c (Var, SensExpr), Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen c ()
connect x y =
  tell
    [ c_entry (annotation y) .=. SetFamily (C_Exit (annotation x)) ]

-- | Combine two nodes, to behave as one
sameNode :: (c (Var, SensExpr), Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen c ()
sameNode x y =
  tell
    [ c_entry (annotation x) .=. SetFamily (C_Entry (annotation y))
    , c_exit  (annotation x) .=. SetFamily (C_Exit  (annotation y))
    ]

-- TODO: Connect to following nodes
handleFunDef :: c (Var, SensExpr) => CFunctionDef NodeId -> ConstraintGen c ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ c_exit (annotation e) .=. SetEmpty
    , c_entry (annotation stmt) .=. SetFamily (c_exit (annotation e))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: c (Var, SensExpr) => CExternalDeclaration NodeId -> ConstraintGen c ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: c (Var, SensExpr) => (CTranslationUnit NodeId, NodeId) -> ConstraintGen c ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

