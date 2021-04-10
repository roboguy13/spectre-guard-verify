{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -Wno-orphans #-}

module Orphans where

import           Language.C

import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Traversable

traverseF :: (Applicative f, Traversable t1, Traversable t2) => (a -> f b) -> t1 (t2 a) -> f (t1 (t2 b))
traverseF f x = sequenceA (fmap (traverse f) x)

instance Foldable CStatement where
  foldMap = foldMapDefault

instance Traversable CStatement where
  traverse f (CLabel ident stmt attrs x) = CLabel <$> pure ident <*> traverse f stmt <*> traverse (traverse f) attrs <*> f x
  traverse f (CCase expr stmt x) = CCase <$> traverse f expr <*> traverse f stmt <*> f x
  traverse f (CCases exprA exprB stmt x) = CCases <$> traverse f exprA <*> traverse f exprB <*> traverse f stmt <*> f x

  traverse f (CDefault stmt x) = CDefault <$> traverse f stmt <*> f x
  traverse f (CExpr m x) = CExpr <$> traverseF f m <*> f x
  traverse f (CCompound idents items x) = CCompound <$> pure idents <*> traverse (traverse f) items <*> f x

  traverse f (CIf expr stmt stmt_maybe x) = CIf <$> traverse f expr <*> traverse f stmt <*> traverseF f stmt_maybe <*> f x

  traverse f (CSwitch expr stmt x) = CSwitch <$> traverse f expr <*> traverse f stmt <*> f x
  traverse f (CWhile expr stmt b x) = CWhile <$> traverse f expr <*> traverse f stmt <*> pure b <*> f x

  traverse f (CFor expr_decl expr_maybeA expr_maybeB stmt x) =
    CFor <$> bisequenceA (bimap (traverseF f) (traverse f) expr_decl) <*> traverseF f expr_maybeA <*> traverseF f expr_maybeB <*> traverse f stmt <*> f x

  traverse f (CGoto ident x) = CGoto <$> pure ident <*> f x
  traverse f (CGotoPtr expr x) = CGotoPtr <$> traverse f expr <*> f x
  traverse f (CCont x) = CCont <$> f x
  traverse f (CBreak x) = CBreak <$> f x
  traverse f (CReturn expr_maybe x) = CReturn <$> traverseF f expr_maybe <*> f x
  traverse f (CAsm astmt x) = CAsm <$> traverse f astmt <*> f x

deriving instance Foldable CAssemblyOperand
deriving instance Foldable CAssemblyStatement
deriving instance Foldable CCompoundBlockItem
deriving instance Foldable CStringLiteral
deriving instance Foldable CArraySize
deriving instance Foldable CDerivedDeclarator
deriving instance Foldable CDeclarator
deriving instance Foldable CAlignmentSpecifier
deriving instance Foldable CFunctionSpecifier
deriving instance Foldable CTypeQualifier
deriving instance Foldable CEnumeration
deriving instance Foldable CBuiltinThing
deriving instance Foldable CInitializer
deriving instance Foldable CPartDesignator
deriving instance Foldable CConstant
deriving instance Foldable CExpression
deriving instance Foldable CAttribute
deriving instance Foldable CStructureUnion
deriving instance Foldable CTypeSpecifier
deriving instance Foldable CStorageSpecifier
deriving instance Foldable CDeclarationSpecifier
deriving instance Foldable CFunctionDef
deriving instance Foldable CDeclaration
deriving instance Foldable CExternalDeclaration
deriving instance Foldable CTranslationUnit

deriving instance Traversable CAssemblyOperand
deriving instance Traversable CAssemblyStatement
deriving instance Traversable CCompoundBlockItem
deriving instance Traversable CStringLiteral
deriving instance Traversable CArraySize
deriving instance Traversable CDerivedDeclarator
deriving instance Traversable CDeclarator
deriving instance Traversable CAlignmentSpecifier
deriving instance Traversable CFunctionSpecifier
deriving instance Traversable CTypeQualifier
deriving instance Traversable CEnumeration
deriving instance Traversable CBuiltinThing
deriving instance Traversable CInitializer
deriving instance Traversable CPartDesignator
deriving instance Traversable CConstant
deriving instance Traversable CExpression
deriving instance Traversable CAttribute
deriving instance Traversable CStructureUnion
deriving instance Traversable CTypeSpecifier
deriving instance Traversable CStorageSpecifier
deriving instance Traversable CDeclarationSpecifier
deriving instance Traversable CFunctionDef
deriving instance Traversable CDeclaration
deriving instance Traversable CExternalDeclaration
deriving instance Traversable CTranslationUnit
