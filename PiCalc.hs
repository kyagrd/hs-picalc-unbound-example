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
import           Data.Map.Strict         hiding (insert, map, mapMaybe, null,
                                          union, (\\))
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Data.Set                (Set (..))
import qualified Data.Set                as S
import           Unbound.LocallyNameless

type Nm = Name Tm
type Sym = String

data Tm = V Nm | D Sym [Tm] deriving (Eq,Ord,Show)
data Eqn = Eq Tm Tm deriving Show


data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB | Match Tm Tm Pr
         | Let (Bind (Tm, Embed Tm) Pr)
         | Plus Pr Pr | Par Pr Pr | Nu PrB  deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr
instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare
instance Eq (Bind (Tm, Embed Tm) Pr) where (==) = aeqBinders
instance Ord (Bind (Tm, Embed Tm) Pr) where compare = acompare

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

mstep :: Monad m => ([Eqn], Map Nm Tm) -> m ([Eqn], Map Nm Tm)
mstep (t1@(D f1 ts1) `Eq` t2@(D f2 ts2) : es, s)
  | f1==f2 && length ts1==length ts2 = return (zipWith Eq ts1 ts2 ++ es, s)
  | otherwise = fail $ show t1 ++" /= " ++ show t2
mstep (V x `Eq` t : es, s)
  | occurs x t' = fail $ show x ++" occurs in "++show t
                      ++ let t' = expand s t in
                          if t /= t' then ", that is, "++show t' else ""
  | M.member x s = fail $ show x ++" is not fresh in "++show s
  | otherwise = return (es, s')
    where
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)

-- unification
uni :: Monad m => ([Eqn], Map Nm Tm) -> m (Map Nm Tm)
uni ([], s) = return s
uni (es, s) = uni =<< ustep (es, s)

-- matching (left pattern matches right term)
mat :: Monad m => ([Eqn], Map Nm Tm) -> m (Map Nm Tm)
mat ([], s) = return s
mat (es, s) = mat =<< mstep (es, s)



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
          s1 <- uni ([l `Eq` atPos pos t],emptyMap)
          let s2 = F.foldr extend s (M.toList s1)
          let subs = expand s1
          return (plugPos (subs t) pos (subs r), poss\\[pos], s2)
     where
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
     s <- uni ([t1' `Eq ` t2'], s)
     return $ M.filterWithKey (\k _ -> k `elem` fvs) s
  where
  fvs = nub $ fv (t1,t2) :: [Nm]


-- TODO reduce fucntion ???




type Knw = [Tm]

syn knw t@(V x) = t `elem` knw
syn knw (D "pair" [t1, t2]) = syn knw t1 && syn knw t2
syn knw t@(D "enc" [t1, t2]) | syn knw t2 = syn knw t1
                             | otherwise = t `elem` knw

newKnw :: Tm -> Knw -> Knw
newKnw t@(V _) knw
  | syn knw t  = []
  | otherwise = nub . concat $ (nub . uncurry newKnw) <$> xknws
  where
    xknws = do { x <- knw; return (x, t : (knw \\ [x])) }
newKnw t@(D "pair" [t1, t2]) knw
  | syn knw t  = []
  | syn knw t1 = t2new
  | syn knw t2 = t1new
  | otherwise  = nub . concat $ (nub . uncurry newKnw) <$> xknws
  where
    t1new = nub $ newKnw t1 knw
    t2new = nub $ newKnw t2 knw
    t12new = t1new `union` t2new
    xknws = do { x <- knw; return (x, t12new ++ (knw \\ [x])) }
newKnw t@(D "enc" [t1, t2]) knw
  | syn knw t  = []
  | syn knw t2 = newKnw t1 knw
  | otherwise = nub . concat $ (nub . uncurry newKnw) <$> xknws
  where
    xknws = do { x <- knw; return (x, t : (knw \\ [x])) }

addKnw :: Tm -> Knw -> Knw
addKnw t knw = newKnw t knw `union` knw
