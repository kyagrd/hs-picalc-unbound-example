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
  -- | Bang Pr -- not implemented at the moment
  | Par Pr Pr
  | Plus Pr Pr
  | Match Tm Tm Pr
  deriving (Ord, Show)

data Act  = Up Tm Tm | Dn Tm Tm | Tau deriving (Eq, Ord, Show)
data ActB = UpB Tm   | DnB Tm         deriving (Eq, Ord, Show)

data Formula = TT | FF | Conj [Formula] | Disj [Formula]
  | Dia Act Formula | Box Act Formula
  | DiaB ActB (Bind NameTm Formula) | BoxB ActB (Bind NameTm Formula)
  | DiaMatch [(Tm,Tm)] Formula | BoxMatch [(Tm,Tm)] Formula
  deriving (Eq,Ord,Show)

-- lambda-Prolog like infix bind notiation
infixr 1 .\
(.\) = bind

-- infix and lowercase names for convenience
infixl 6 .+
(.+) = Plus
infixl 5 .|
(.|) = Par

o = Null
tau = TauP Null
taup = TauP
inp x = In (Var x)
out x y = Out (Var x) (Var y)
match x y = Match (Var x) (Var y)
nu = Nu

conj, disj :: [Formula] -> Formula

conj []  = TT
conj [f] = f
conj fs  = Conj fs

disj []  = FF
disj [f] = f
disj fs  = Disj fs

instance Eq Pr where (==) = aeq
instance Eq (Bind NameTm Pr) where (==) = aeqBinders
instance Ord (Bind NameTm Pr) where compare = acompare
instance Eq (Bind NameTm Formula) where (==) = aeqBinders
instance Ord (Bind NameTm Formula) where compare = acompare

 -- tried to infix Par and Plus as (:|:) (:+:) but TH error, maybe from Replib
$(derive [''Tm, ''Act, ''ActB, ''Pr, ''Formula])

instance Alpha Tm
instance Alpha Pr
instance Alpha Act
instance Alpha ActB
instance Alpha Formula

instance Subst Tm Tm where
  isvar (Var v) = Just (SubstName v)
  -- isvar _       = Nothing

instance Subst Tm Pr where
instance Subst Tm Act where
instance Subst Tm ActB where
instance Subst Tm Formula where

---- if you are to define unification kind of thing with Hashmap
-- instance Hashable NamePr where
--   hashWithSalt s n = hashWithSalt s (name2String n, name2Integer n)

-- assming there is exactly one NameTm binding for both
unbind2' b1 b2 = do { Just (x,p1,_,p2) <- unbind2 b1 b2; return (x,p1,p2) }
