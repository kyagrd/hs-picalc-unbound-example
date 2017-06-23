{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module PiCalc where
import Data.Maybe
import Data.List
import Data.List.Ordered (nubSort)
import Unbound.LocallyNameless

type Nm = Name Tm
newtype Tm = Var Nm deriving (Eq, Ord, Show)

data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB | Match Tm Tm Pr
         | Plus Pr Pr | Par Pr Pr | Nu PrB  deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr
instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare

data Act   = Up Tm Tm  | Tau     deriving (Eq, Ord, Show)
data ActB  = UpB Tm    | DnB Tm  deriving (Eq, Ord, Show)

data Form  = FF | TT | Conj [Form] | Disj [Form]
           | Dia  Act Form  |  DiaB  ActB FormB   | DiaMatch [(Tm,Tm)] Form
           | Box  Act Form  |  BoxB  ActB FormB   | BoxMatch [(Tm,Tm)] Form
           deriving (Eq,Ord,Show)
type FormB = Bind Nm Form
instance Eq FormB where (==) = aeqBinders
instance Ord FormB where compare = acompare

$(derive [''Tm, ''Act, ''ActB, ''Pr, ''Form])

instance Alpha Tm; instance Alpha Act; instance Alpha ActB
instance Alpha Pr; instance Alpha Form

instance Subst Tm Tm where isvar (Var x) = Just (SubstName x)
instance Subst Tm Act;  instance Subst Tm ActB
instance Subst Tm Pr;  instance Subst Tm Form

infixr 1 .\
(.\) = bind

x .= y = Match (Var x) (Var y)
inp = In . Var
out x y = Out(Var x)(Var y)
tau = TauP Null
tautau = TauP (TauP Null)

conj  = cn . filter(/=TT) where cn  [] = TT; cn  [f] = f; cn  fs = Conj fs
disj  = ds . filter(/=FF) where ds  [] = FF; ds  [f] = f; ds  fs = Disj fs

unbind2' b1 b2 = do  Just (x,p1,_,p2) <- unbind2 b1 b2
                     return (x,p1,p2)
(.+)  = Plus  ;   infixl 6 .+
(.|)  = Par   ;  infixl 5 .|
o = Null
taup = TauP
nu = Nu



------------------------------------------------------------------
-- transformation/reduction of processes via generic programming
------------------------------------------------------------------

removeNull :: Rep a => a -> a
removeNull a = case cast a of
  Just(Plus Null x) -> fromJust(cast x)
  Just(Plus x Null) -> fromJust(cast x)
  Just(Par Null x) -> fromJust(cast x)
  Just(Par x Null) -> fromJust(cast x)
  _ -> a

-- rotate right for associative operators Plus and Par
rotateRight :: Rep a => a -> a
rotateRight a = case cast a of
  Just(Plus (Plus x y) z) -> fromJust . cast $ Plus x (Plus y z)
  Just(Par (Par x y) z) -> fromJust . cast $ Par x (Par y z)
  _ -> a

-- nub/sort for commutative operators Plus and Par
nubSortComm :: Rep a => a -> a
nubSortComm a = case cast a of
  Just p@(Plus _ _) -> fromJust . cast . foldr1 Plus . nubSort $
    unfoldr (\q -> case q of { Plus x y -> Just(x,y) ; _ -> Nothing }) p
  Just p@(Par _ _) -> fromJust . cast . foldr1 Par . nubSort $
    unfoldr (\q -> case q of { Par x y -> Just(x,y) ; _ -> Nothing }) p
  _ -> a

simplify = everywhere nubSortComm
         . everywhere rotateRight
         . everywhere removeNull

{-
foldl1 Plus (replicate 3 $ foldl1 Par [Null,Null,Null])
everywhere rotateRight $ foldl1 Plus (replicate 3 $ foldl1 Par [Null,Null,Null])
red $ foldl1 Plus (replicate 3 $ foldl1 Par [Null,Null,Null])
-}

