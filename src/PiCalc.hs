{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module PiCalc where

import           Unbound.LocallyNameless


{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

type NameTm = Name Tm

-- names are the only terms in pi-calc
newtype Tm = Var NameTm deriving (Eq, Ord, Show)

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
  deriving Show

data Act  = Up Tm Tm | Dn Tm Tm | Tau deriving (Eq, Ord, Show)
data ActB = UpB Tm   | DnB Tm         deriving (Eq, Ord, Show)

instance Eq Pr where (==) = aeq

$(derive [''Tm, ''Pr]) -- tried to infix Par as (:|:) but illegal TH thing

instance Alpha Tm
instance Alpha Pr

instance Subst Tm Tm where
  isvar (Var v) = Just (SubstName v)
  -- isvar _       = Nothing

instance Subst Tm Pr where

---- if you are to define unification kind of thing with Hashmap
-- instance Hashable NamePr where
--   hashWithSalt s n = hashWithSalt s (name2String n, name2Integer n)
