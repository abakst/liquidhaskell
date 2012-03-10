{-# LANGUAGE DeriveDataTypeable, RankNTypes, GADTs #-}

module Language.Haskell.Liquid.Measure (  
    Spec (..)
  , MSpec (..)
  , Measure (name, sort)
  , Def (..)
  , Body (..)
  , mkM, mkMSpec
  , qualifySpec
  , mapTy
  , dataConTypes
 -- , measuresSpec
  ) where

import GHC
import Var
import Outputable
import DataCon
import Data.Map hiding (null, partition)
import Data.Data
import Data.Monoid hiding ((<>))
import Data.List (partition)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType

data Spec ty bndr  = Spec { 
    measures   :: [Measure ty bndr]     -- User-defined properties for ADTs
  , assumes    :: [(Symbol, ty)]        -- Imported functions and types   
  , imports    :: [Symbol] 
  } deriving (Data, Typeable)

data MSpec ty bndr = MSpec { 
    ctorMap :: Map Symbol [Def bndr]
  , measMap :: Map Symbol (Measure ty bndr) 
  } deriving (Data, Typeable)

data Measure ty bndr = M { 
    name :: Symbol
  , sort :: ty
  , eqns :: [Def bndr]
  } deriving (Data, Typeable)

data Def bndr 
  = Def { 
    measure :: Symbol
  , ctor    :: bndr
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Data, Typeable)

data Body 
  = E Expr 
  | P Pred
  deriving (Data, Typeable)


-- TODO
qualifySpec :: Symbol -> Spec ty bndr -> Spec ty bndr
qualifySpec specname x = x 

mkM :: Symbol -> ty -> [Def bndr] -> Measure ty bndr
mkM name typ eqns 
  | all ((name ==) . measure) eqns
  = M name typ eqns
  | otherwise
  = error $ "invalid measure definition for " ++ (show name)

mkMSpec ms = MSpec cm mm 
  where cm  = groupMap ctor $ concatMap eqns ms'
        mm  = fromList [(name m, m) | m <- ms' ]
        ms' = checkFail "Duplicate Measure Definition" (distinct . fmap name) ms

instance Monoid (Spec ty bndr) where
  mappend (Spec xs ys zs) (Spec xs' ys' zs')
           = Spec (xs ++ xs') (ys ++ ys') (nubSort (zs ++ zs'))
  mempty   = Spec [] [] []

instance Functor Def where
  fmap f def = def { ctor = f (ctor def) }

instance Functor (Measure t) where
  fmap f (M n s eqs) = M n s (fmap (fmap f) eqs)

instance Functor (MSpec t) where
  fmap f (MSpec cm mm) = MSpec (fc cm) (fm mm)
     where fc = fmap $ fmap $ fmap f
           fm = fmap $ fmap f 

instance Outputable Body where
  ppr (E e) = toFix e  
  ppr (P p) = toFix p

instance Outputable a => Outputable (Def a) where
  ppr (Def m c bs body) = ppr m <> text " " <> pprPat (c, bs) <> text " = " <> ppr body   
    where pprPat (c, bs) = parens (ppr c <> hsep (ppr `fmap` bs))

instance (Outputable t, Outputable a) => Outputable (Measure t a) where
  ppr (M n s eqs) =  ppr n <> text "::" <> ppr s
                  $$ vcat (ppr `fmap` eqs)

instance (Outputable t, Outputable a) => Outputable (MSpec t a) where
  ppr =  vcat . fmap ppr . fmap snd . toList . measMap


mapTy :: (a -> b) -> Measure a c -> Measure b c
mapTy f (M n ty eqs) = M n (f ty) eqs


dataConTypes :: MSpec RefType DataCon -> ([(Var, RefType)], [(Symbol, RefType)])
dataConTypes s = (ctorTys, measTys)
  where measTys = [(name m, sort m) | m <- elems $ measMap s]
        ctorTys = [(defsVar ds, defsTy ds) | (_, ds) <- toList $ ctorMap s]
        defsTy  = reduce strengthenRefType . fmap defRefType 
        defsVar = dataConWorkId . ctor . safeHead "defsVar" 

defRefType :: Def DataCon -> RefType
defRefType (Def f dc xs body) = mkArrow as xts t'
  where as  = dataConUnivTyVars dc
        xts = safeZip "defRefType" xs $ ofType `fmap` dataConOrigArgTys dc
        t'  = refineWithCtorBody dc f body t 
        t   = ofType $ dataConOrigResTy dc

refineWithCtorBody dc f body t = 
  case stripRTypeBase t of 
    Just (Reft (v, ras)) ->
      strengthen t $ Reft (v, [RConc $ bodyPred v body])
    Nothing -> 
      error $ "measure mismatch " ++ showPpr f ++ " on con " ++ showPpr dc
  where bodyPred v (E e) = PAtom Eq (EApp f [EVar v]) e
        bodyPred v (P p) = PIff  (PBexp (EApp f [EVar v])) p 

--measuresSpec ::  [Measure ty bndr] -> Spec ty bndr
--measuresSpec ms = Spec ms' bs 
--  where (ms', ms'') = partition (not . null . eqns) ms
--        bs          = [(name m, sort m) | m <- ms'']
