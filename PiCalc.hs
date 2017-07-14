{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module PiCalc where
import           Data.List.Ordered       (nubSort)
import           Data.Maybe
import           Unbound.LocallyNameless
import           Data.List               hiding (insert, map, null)
import           Data.Map.Strict         hiding (insert, map, mapMaybe, null)
import qualified Data.Map.Strict as M

type Nm = Name Tm
type Sym = String

data Tm = V Nm | D Sym [Tm] deriving (Eq,Ord,Show)
data Eqn = Eq Tm Tm deriving Show


data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB | Match Tm Tm Pr
         | Plus Pr Pr | Par Pr Pr | Nu PrB  deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr
instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare

data Act   = Up Tm Tm  | Tau     deriving (Eq, Ord, Show)
data ActB  = UpB Tm    | DnB Tm  deriving (Eq, Ord, Show)
{-
data Form  = FF | TT | Conj [Form] | Disj [Form]
           | Dia  Act Form  |  DiaB  ActB FormB   | DiaMatch [(Tm,Tm)] Form
           | Box  Act Form  |  BoxB  ActB FormB   | BoxMatch [(Tm,Tm)] Form
           deriving (Eq,Ord,Show)
type FormB = Bind Nm Form
instance Eq FormB where (==) = aeqBinders
instance Ord FormB where compare = acompare
-}
-- $(derive [''Tm, ''Eqn, ''Act, ''ActB, ''Pr, ''Form])
$(derive [''Tm, ''Eqn, ''Act, ''ActB, ''Pr])

instance Alpha Tm; instance Alpha Eqn
instance Alpha Act; instance Alpha ActB
instance Alpha Pr; -- instance Alpha Form

instance Subst Tm Tm where
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing
instance Subst Tm Eqn
instance Subst Tm Act;  instance Subst Tm ActB
instance Subst Tm Pr; -- instance Subst Tm Form

occurs x t = x `elem` (fv t :: [Nm])

infixr 1 .\
(.\) = bind

x .= y = Match (V x) (V y)
inp = In . V
out x y = Out(V x)(V y)
tau = TauP Null
tautau = TauP (TauP Null)

-- conj  = cn . filter(/=TT) where cn  [] = TT; cn  [f] = f; cn  fs = Conj fs
-- disj  = ds . filter(/=FF) where ds  [] = FF; ds  [f] = f; ds  fs = Disj fs

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
  Just(Par Null x)  -> fromJust(cast x)
  Just(Par x Null)  -> fromJust(cast x)
  _                 -> a

-- rotate right for associative operators Plus and Par
rotateRight :: Rep a => a -> a
rotateRight a = case cast a of
  Just(Plus (Plus x y) z) -> fromJust . cast $ Plus x (Plus y z)
  Just(Par (Par x y) z)   -> fromJust . cast $ Par x (Par y z)
  _                       -> a

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




{-
Alternative implemntation of the rule-based unfication algorithm U
from the unfication chapter of the "handbook of automated reasoning"
http://www.cs.bu.edu/~snyder/publications/UnifChapter.pdf
Instead of applying to the unification to the rest of the equation es,
make a feedback when there already exists a mapping from same variable.
Becuase the variables in the equations are not substituted by the current
substitution, we need to use a helper function expand that expand terms
according to the current substitution.
-}

expand s (V x) = case M.lookup x s of { Nothing -> V x; Just u -> expand s u }
expand s (D f ts) = D f (expand s <$> ts)

ustep :: Monad m => ([Eqn], Map Nm Tm) -> m ([Eqn], Map Nm Tm)
ustep (t1@(D f1 ts1) `Eq` t2@(D f2 ts2) : es, s)
  | f1==f2 && length ts1==length ts2 = return (zipWith Eq ts1 ts2 ++ es, s)
  | otherwise = fail $ show t1 ++" /= " ++ show t2
ustep (t1@(D _ _) `Eq` t2@(V x) : es, s) = return (t2 `Eq` t1 : es, s)
ustep (t1@(V x) `Eq` t2@(V y) : es, s)
  | x == y = return (es, s)
  | x > y = ustep (t2 `Eq` t1 : es, s)
ustep (V x `Eq` t : es, s)
  | occurs x t' = fail $ show x ++" occurs in "++show t
                      ++ let t' = expand s t in
                          if t /= t' then ", that is, "++show t' else ""
  | M.member x s = return (s!x `Eq` t' : es, s')
  | otherwise = return (es, s')
    where
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)

u :: Monad m => ([Eqn], Map Nm Tm) -> m (Map Nm Tm)
u ([], s) = return s
u (es, s) = u =<< ustep (es, s)
