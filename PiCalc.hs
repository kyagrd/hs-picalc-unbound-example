{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module PiCalc where
import           Control.Applicative
import           Data.Foldable           as F
import           Data.List               (nub, (\\))
import           Data.List               hiding (insert, map, null, union)
import           Data.List.Ordered       (nubSort)
import           Data.Map.Strict         hiding (foldr, insert, map, mapMaybe,
                                          null, union, (\\))
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Data.Set                (Set (..))
import qualified Data.Set                as S
import           Unbound.LocallyNameless hiding (Con)
{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}
type Nm = Name Tm
type Sym = String

data Tm = V Nm | D Sym [Tm] deriving (Eq,Ord,Show)
type Eqn = (Tm,Tm)


data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB | Match Tm Tm Pr
         | Let (Bind (Tm, Embed Tm) Pr)
         | Plus Pr Pr | Par Pr Pr | Nu PrB  deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr

data Ag  = Con Tm Pr | Abs PrB | New AgB deriving (Eq, Ord, Show)
type AgB = Bind Nm Ag

instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare
instance Eq (Bind (Tm, Embed Tm) Pr) where (==) = aeqBinders
instance Ord (Bind (Tm, Embed Tm) Pr) where compare = acompare

instance Eq AgB where (==) = aeqBinders
instance Ord AgB where compare = acompare


data Act   = Up Tm | Dn Tm | Tau     deriving (Eq, Ord, Show)
{-
data Form  = FF | TT | Conj [Form] | Disj [Form]
           | Dia  Act Form  |  DiaB  ActB FormB   | DiaMatch [(Tm,Tm)] Form
           | Box  Act Form  |  BoxB  ActB FormB   | BoxMatch [(Tm,Tm)] Form
           deriving (Eq,Ord,Show)
type FormB = Bind Nm Form
instance Eq FormB where (==) = aeqBinders
instance Ord FormB where compare = acompare
-}
-- $(derive [''Tm, ''Act, ''ActB, ''Pr, ''Form])
$(derive [''Tm, ''Act, ''Pr, ''Ag])

instance Alpha Tm
instance Alpha Act
instance Alpha Pr; -- instance Alpha Form
instance Alpha Ag

instance Subst Tm Tm where
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing
instance Subst Tm Act
instance Subst Tm Pr; -- instance Subst Tm Form
instance Subst Tm Ag

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



unifyWith, matchWith :: Monad m =>
  ( ([Eqn], Map Nm Tm) -> m ([Eqn], Map Nm Tm) )
  -> [Eqn] -> Map Nm Tm -> m (Map Nm Tm)
-- unification
unifyWith step [] s = return s
unifyWith step es s = uncurry (unifyWith step) =<< step (es, s)
-- matching (left pattern matches right term)
matchWith step [] s = return s
matchWith step es s = uncurry (matchWith step) =<< step (es, s)

-- uni = unifyWith ustep
-- mat = matchWith mstep

ustep :: Monad m => ([Eqn], Map Nm Tm) -> m ([Eqn], Map Nm Tm)
ustep ((t1@(D f1 ts1),t2@(D f2 ts2)) : es, s)
  | f1==f2 && length ts1==length ts2 = return (zip ts1 ts2 ++ es, s)
  | otherwise = fail $ show t1 ++" /= " ++ show t2
ustep ((t1@(D _ _),t2@(V x)) : es, s) = return ((t2,t1) : es, s)
ustep ((t1@(V x),t2@(V y)) : es, s)
  | x == y = return (es, s)
  | x > y = ustep ((t2,t1) : es, s)
ustep ((V x, t) : es, s)
  | occurs x t' = fail $ show x ++" occurs in "++show t
                      ++ let t' = expand s t in
                          if t /= t' then ", that is, "++show t' else ""
  | M.member x s = return ((s!x, t') : es, s')
  | otherwise = return (es, s')
    where
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)

mstep :: Monad m => ([Eqn], Map Nm Tm) -> m ([Eqn], Map Nm Tm)
mstep ((t1@(D f1 ts1),t2@(D f2 ts2)) : es, s)
  | f1==f2 && length ts1==length ts2 = return (zip ts1 ts2 ++ es, s)
  | otherwise = fail $ show t1 ++" /= " ++ show t2
mstep ((V x, t): es, s)
  | occurs x t' = fail $ show x ++" occurs in "++show t
                      ++ let t' = expand s t in
                          if t /= t' then ", that is, "++show t' else ""
  | M.member x s = fail $ show x ++" is not fresh in "++show s
  | otherwise = return (es, s')
    where
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)


emptyMap = M.empty

x,y,z :: Nm
x = s2n "x"
y = s2n "y"
z = s2n "z"




-- following are all aeq
aaa = permbind (nub $ fv rule1 :: [Nm]) rule1
bbb = permbind [x,y] rule1
ccc = permbind [y,x] rule1
ddd = rulebind rule1


rulebind rule = permbind (nub $ fv rule :: [Nm]) rule



ruleSet = map rulebind [rule1,rule2,rule3]

dec = D"dec"
enc = D"enc"
rule1 = (dec[enc[V x,V y], V y],  V x)
rule2 = (D"fst"[D"pair"[V x,V y]], V x)
rule3 = (D"snd"[D"pair"[V x,V y]], V y)
ruleSet1 = map rulebind [rule1]


mytmDec2 = D"_"[dec[V x,V y],dec[V z,V y]]
mytmDec1 = dec[V x,V y]
mytmDec1' = D"_"[mytmDec1,V x,V y]

ruleSet2 = map rulebind
  [ (D"h"[D"f"[V x],V y],  V y)
  , (D"h"[D"g"[V x],V y],  V y)
  ]

mytmH' = D"_"[mytmH,V x,V y]
mytmH = h[V x,V y] where h=D"h"

data Pos = PR | PD Int Pos deriving (Eq,Ord,Show)

plugPos _        PR         v = v
plugPos (D f ts) (PD k pos) v = D f $ ts1 ++ plugPos u pos v : ts2
  where (ts1,u:ts2) = splitAt k ts

subterm t@(V _)    = return (PR, t)
subterm t@(D f []) = return (PR, t)
subterm t@(D f ts) = return (PR, t) <|>
  do k <- [0 .. length ts - 1]
     (pos, v) <- subterm (ts!!k)
     return (PD k pos, v)

-- non variable positions only
subtermInit t = do { r@(pos, D _ _) <- subterm t; return pos }

atPos PR         t        = t
atPos (PD k pos) (D _ ts) = atPos pos (ts!!k)

-- implementation of narrowing from
-- https://pdfs.semanticscholar.org/1803/a29f9588026a731a1baf4cc61a0d328d3e06.pdf
narrBy rules (t,poss,s) =
  do pos <- poss
     rule <- rules
     runFreshMT $
       do mapM_ fresh (nub $ fv t :: [Nm])
          (_,(l,r)) <- unbind rule
          s1 <- uni [(l, atPos pos t)] emptyMap
          let s2 = F.foldr extend s (M.toList s1)
          let subs = expand s1
          return (plugPos (subs t) pos (subs r), poss\\[pos], s2)
     where
       uni = unifyWith ustep
       extend (x,t) s = let t' = expand s t
                         in M.insert x t' (subst x t' <$> s)

kleeneClosure step x = return x <|> transClosure step x
transClosure step x = xs' <|> asum (transClosure step <$> xs')
  where xs' = step x

subvariant rules t =
  (\(a,_,c)->(a,c)) <$> kleeneClosure (narrBy rules) (t, subtermInit t, emptyMap)


-- example unification (finding unifier modulo subterm convergnet rewriting)
-- basically implmented http://www.lsv.fr/~ciobaca/subvariant/

unifiersModulo rules (t1,t2) =
  do (D"_"[t1',t2'], _, s) <- kleeneClosure (narrBy rules)
                                (D"_"[t1,t2], subtermInit $ D"_"[t1,t2], emptyMap)
     s <- uni [(t1',t2')] s
     return $ M.filterWithKey (\k _ -> k `elem` fvs) s
  where
    uni = unifyWith ustep
    fvs = nub $ fv (t1,t2) :: [Nm]


-- TODO reduce fucntion ???




type Knw = [Tm]

syn [] _         =  False
syn knw@(k:ks) t = syn1 (newKnw k knw `union` knw) t

syn1 knw t@(V x) = t `elem` knw
syn1 knw (D "pair" [t1, t2]) = syn1 knw t1 && syn1 knw t2
syn1 knw t@(D "enc" [t1, t2]) | syn1 knw t2 = syn1 knw t1
                              | otherwise = t `elem` knw

newKnw1 t@(V _) knw
  | syn1 knw t = []
  | otherwise = [t]
newKnw1 (D "pair" [t1, t2]) knw = newKnw1 t1 knw `union` newKnw1 t2 knw
newKnw1 t@(D "enc" [t1, t2]) knw
  | syn1 knw t  = []
  | syn1 knw t2 = newKnw1 t1 knw
  | otherwise  = [t]

moreKnw ts knw = foldr union ts [newKnw1 u (ts++(knw\\[u])) \\ [u] | u <- knw]

newKnw t knw
  | null moreknw = newknw1
  | otherwise = moreknw `union` newKnw t (moreknw `union` knw)
  where
    newknw1 = newKnw1 t knw
    moreknw = moreKnw newknw1 knw

addKnw :: Tm -> Knw -> Knw
addKnw t knw = newKnw t knw `union` knw
