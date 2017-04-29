{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module PiCalc where

import           Unbound.LocallyNameless


{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

type NameTm = Name Tm

-- names are the only terms in pi-calc
newtype Tm = Var NameTm deriving (Eq, Ord, Show)

-- finite pi calculus for now
data Pr
  = Null
  | TauP Pr
  | In Tm (Bind NameTm Pr)
  | Out Tm Tm Pr
  | Nu (Bind NameTm Pr)
  -- | Bang Pr
  | Par Pr Pr
  | Plus Pr Pr
  | Match Tm Tm Pr
  deriving (Ord, Show)

data Act  = Up Tm Tm | Dn Tm Tm | Tau deriving (Eq, Ord, Show)
data ActB = UpB Tm   | DnB Tm         deriving (Eq, Ord, Show)

instance Eq Pr where (==) = aeq
instance Eq (Bind NameTm Pr) where (==) = liftBind2 (==)
instance Ord (Bind NameTm Pr) where compare = liftBind2 compare

liftBind2 op b1 b2 = runFreshM $ do
    (x1,p1) <- unbind b1
    (x2,p2) <- unbind b2
    return $ p1 `op` subst x1 (Var x2) p2

$(derive [''Tm, ''Pr, ''Act, ''ActB]) -- tried to infix Par as (:|:) but illegal TH thing

instance Alpha Tm
instance Alpha Pr

instance Subst Tm Tm where
  isvar (Var v) = Just (SubstName v)
  -- isvar _       = Nothing

instance Subst Tm Pr where
instance Subst Tm Act where
instance Subst Tm ActB where

---- if you are to define unification kind of thing with Hashmap
-- instance Hashable NamePr where
--   hashWithSalt s n = hashWithSalt s (name2String n, name2Integer n)

-- lambda-Prolog like infix bind notiation
(.\) = bind
