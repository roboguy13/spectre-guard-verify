{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

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

-- pattern SensAtom :: Sensitivity -> LatticeExpr f SensExpr'
pattern SensAtom :: c SensExpr' => Sensitivity -> SensExpr c
pattern SensAtom   s  = LatticeVal (LiftedValue (SensAtom' s))

pattern SensFamily :: c SensExpr' => SensFamily a -> SensExpr c
pattern SensFamily sf = LatticeVal' (SensFamily' sf)

-- sensAtom :: Convert t SensExpr' => Sensitivity -> LatticeExpr f SensExpr'
-- sensAtom s = LatticeVal (LiftedValue (SensAtom' s))
-- sensAtom s = latticeVal' (SensAtom' s)
-- sensFamily sf = LatticeVal' (SensFamily' sf)

type SensExpr c = LatticeExpr c (AnalysisSetFamily c) SensExpr'

-- | The set family for this analysis
data AnalysisSetFamily c a where
  C_Entry :: NodeId -> AnalysisSetFamily c (Var, SensExpr c)
  C_Exit :: NodeId -> AnalysisSetFamily c (Var, SensExpr c)

  S_Family :: NodeId -> NodeId -> AnalysisSetFamily c (Var, SensExpr c)
  B_Family :: NodeId -> AnalysisSetFamily c Var

pattern C_Entry' n = SetFamily (C_Entry n)
pattern C_Exit' n = SetFamily (C_Exit n)
pattern S_Family' m n = SetFamily (S_Family m n)
pattern B_Family' n = SetFamily (B_Family n)

-- class AnalysisSfExpr f where
--   c_entry :: NodeId -> f (Var, SensExpr c)
--   c_exit  :: NodeId -> f (Var, SensExpr c)

--   s_family :: NodeId -> NodeId -> f (Var, SensExpr c)
--   b_family :: NodeId -> f Var

-- instance AnalysisSfExpr (AnalysisSetFamily c) where
--   c_entry = C_Entry
--   c_exit = C_Exit
--   s_family n = S n
--   b_family = B

-- instance AnalysisSfExpr (SetExpr c (AnalysisSetFamily c)) where
--   c_entry = SetFamily . c_entry
--   c_exit = SetFamily . c_exit
--   s_family n = SetFamily . s_family n
--   b_family = SetFamily . b_family

type Constraints c = [SomeConstraint c (AnalysisSetFamily c)]


newtype ConstraintGen c a = ConstraintGen (Writer (Constraints c) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints c))


execConstraintGen :: ConstraintGen c a -> Constraints c
execConstraintGen (ConstraintGen g) = execWriter g

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: (c SensExpr', c (Var, SensExpr c)) => CDeclarator NodeId -> ConstraintGen c ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [C_Exit n .=. SetUnionSingle (C_Entry' n) (Var hash, SensAtom Secret)]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [C_Exit n .=. SetUnionSingle (C_Entry' n) (Var hash, (SensAtom Public))]

handleDeclarator e = nop e

handleCompoundItem :: (c SensExpr', c (Var, SensExpr c)) => CCompoundBlockItem NodeId -> ConstraintGen c ()
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

handleExpr :: (c SensExpr', c (Var, SensExpr c)) => CExpression NodeId -> ConstraintGen c ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  handleExpr cv
  tell [ C_Exit n .=. ite (In' (Var x, SensAtom Public) (C_Entry' n))
                                    (SetUnionSingle (C_Entry' n) (Var x, (SensFamily (SensT (annotation e)))))
                                    (C_Entry' n)
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

handleStmt :: (c SensExpr', c (Var, SensExpr c)) => CStatement NodeId -> ConstraintGen c ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ C_Entry (annotation cond) .=. SetFamily (C_Entry l) ]

  tell go

  handleStmt t

  -- tell [atom_e (annotation e0) :=: atom_e (annotation cond)]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,C_Exit l .=. SetUnion (C_Entry' l)
                             (ite (SensFamily (SensT l) `LatticeEqual` SensAtom Secret)
                               (maybeUnion (S_Family' l m) (S_Family' l))
                               (maybeUnion (C_Exit' m) C_Exit'))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = C_Entry (annotation x) .=. SetFamily (C_Entry l)

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
nop :: (c (Var, SensExpr c), Annotated f) => f NodeId -> ConstraintGen c ()
nop e =
  tell
    [ C_Exit (annotation e) .=. SetFamily (C_Entry (annotation e)) ]

connectList :: (c (Var, SensExpr c), Annotated f) => [f NodeId] -> ConstraintGen c ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (c (Var, SensExpr c), Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen c ()
connect x y =
  tell
    [ C_Entry (annotation y) .=. SetFamily (C_Exit (annotation x)) ]

-- | Combine two nodes, to behave as one
sameNode :: (c (Var, SensExpr c), Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen c ()
sameNode x y =
  tell
    [ C_Entry (annotation x) .=. SetFamily (C_Entry (annotation y))
    , C_Exit  (annotation x) .=. SetFamily (C_Exit  (annotation y))
    ]

-- TODO: Connect to following nodes
handleFunDef :: (c SensExpr', c (Var, SensExpr c)) => CFunctionDef NodeId -> ConstraintGen c ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ C_Exit (annotation e) .=. SetEmpty
    , C_Entry (annotation stmt) .=. SetFamily (C_Exit (annotation e))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: (c SensExpr', c (Var, SensExpr c)) => CExternalDeclaration NodeId -> ConstraintGen c ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (c SensExpr', c (Var, SensExpr c)) => (CTranslationUnit NodeId, NodeId) -> ConstraintGen c ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

