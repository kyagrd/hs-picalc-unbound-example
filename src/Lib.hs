{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module Lib where

import           Control.Applicative
-- import           Control.Monad                    (unless)
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
-- import           Data.Graph.Inductive
-- import           Data.Graph.Inductive.Graph
-- import qualified Data.Graph.Inductive.Graph        as Graph
-- import           Data.Graph.Inductive.NodeMap
-- import           Data.Graph.Inductive.PatriciaTree
-- import qualified Data.GraphViz                     as GV
import           Data.List                        (nub, nubBy)
-- import           Data.Partition
-- import qualified Data.Partition                    as Partition
-- import           Data.Set                          (singleton, toList)
-- import           Data.Hashable
-- import qualified Data.HashMap.Strict              as Map
import           Data.Maybe
import           Unbound.LocallyNameless          hiding (empty, fresh, join)
import qualified Unbound.LocallyNameless          as LN


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

{-
% Finite pi-calculus specification in lambda-Prolog
% A specification of the late transition system for the pi calculus.

% bound input
oneb (in X M) (dn X) M.

% free output
one (out X Y P) (up X Y) P.

% tau
one  (taup P) tau P.

% match prefix
one  (match X X P) A Q :- one  P A Q.
oneb (match X X P) A M :- oneb P A M.

% sum
one  (plus P Q) A R :- one  P A R.
one  (plus P Q) A R :- one  Q A R.
oneb (plus P Q) A M :- oneb P A M.
oneb (plus P Q) A M :- oneb Q A M.

% par
one  (par P Q) A (par P1 Q) :- one P A P1.
one  (par P Q) A (par P Q1) :- one Q A Q1.
oneb (par P Q) A (x\par (M x) Q) :- oneb P A M.
oneb (par P Q) A (x\par P (N x)) :- oneb Q A N.

% restriction
one  (nu x\P x) A (nu x\Q x)      :- pi x\ one  (P x) A (Q x).
oneb (nu x\P x) A (y\ nu x\Q x y) :- pi x\ oneb (P x) A (y\ Q x y).

% open
oneb (nu x\M x) (up X) N :- pi y\ one (M y) (up X y) (N y).

% close
one (par P Q) tau (nu y\ par (M y) (N y)) :- oneb P (dn X) M , oneb Q (up X) N.
one (par P Q) tau (nu y\ par (M y) (N y)) :- oneb P (up X) M , oneb Q (dn X) N.

% comm
one (par P Q) tau (par (M Y) T) :-  oneb P (dn X) M, one Q (up X Y) T.
one (par P Q) tau (par R (M Y)) :-  oneb Q (dn X) M, one P (up X Y) R.
-}

one (Out x y p)   = return (Up x y, p)
one (TauP p)      = return (Tau, p)
one (Match x y p) | x == y = one p
one (Plus p q) = one p <|> one q
one (Par p q)
   = do { (l, p') <- one p; return (l, Par p' q) }
 <|> do { (l, q') <- one q; return (l, Par p q') }
 <|> do (lp, bp) <- oneb p
        (lq, bq) <- oneb q
        case (lp, lq) of
          (DnB x, UpB y) | x == y
                         -> do (w, p') <- unbind bp
                               (v, q') <- unbind bq
                               let p'' = subst w (Var v) p'
                               return (Tau, Nu (bind v $ Par p'' q')) -- close
          (UpB x, DnB y) | x == y
                         -> do (v, p') <- unbind bp
                               (w, q') <- unbind bq
                               let q'' = subst w (Var v) q'
                               return (Tau, Nu (bind v $ Par p' q'')) -- close
          _              -> empty
 <|> do (lp, bp) <- oneb p
        (lq, q') <- one q
        case (lp, lq) of
          (DnB x, Up y v) | x == y
                          -> do (w, p') <- unbind bp
                                return (Tau, Par (subst w v p') q') -- comm
          _               -> empty
 <|> do (lp, p') <- one p
        (lq, bq) <- oneb q
        case (lp, lq) of
          (Up y v, DnB x) | x == y
                          -> do (w, q') <- unbind bq
                                return (Tau, Par p' (subst w v q')) -- comm
          _               -> empty
one (Nu b) = do (x,p) <- unbind b
                (l,p') <- one p
                return (l, Nu (bind x p'))
one _ = empty


oneb (In x p)      = return (DnB x, p)
oneb (Match x y p) | x == y = oneb p
oneb (Plus p q)    = oneb p <|> oneb q
oneb (Par p q)
   = do { (l,b') <- oneb p; (x,p') <- unbind b'; return (l, bind x $ Par p' q) }
 <|> do { (l,b') <- oneb q; (x,q') <- unbind b'; return (l, bind x $ Par p q') }
oneb (Nu b)
   = do (x,p) <- unbind b
        (l,b') <- oneb p
        (y,p') <- unbind b'
        return (l, bind y $ Nu (bind x p')) -- restriction
     -- open
 <|> do (x,p) <- unbind b
        (l,p') <- one p
        case l of Up y x' | Var x == x' -> return (UpB y, bind x p')  -- open
                  _       -> empty
oneb _ = empty










{-
-------------------------------------------------------------

maxVal :: Int
maxVal = 3

p0 :: Partition Int
p0 = fromDisjointSets (fmap singleton [0..maxVal])

p1 = joinElems 1 3 p0
p2 = joinElems 2 4 p0
p3 = joinElems 2 3 p1
p4 = joinElems 3 4 p2
p5 = joinElems 1 2 p4

type G = Gr (Partition Int) (Int,Int)

emptyG :: G
emptyG = Graph.empty

g0' :: G
g0' = mkGraph [(0,p0)] []

nodeMap0' = fromGraph g0'
-- mmm = new
-- Graph
-- joinElemsG g x1 x2 p =
--  where p' = joinElems x1 x2 p

(g0,nodeMap0,lnode0) = insMapNode new p0 emptyG

(g1,nodeMap1) = (insMapEdge nm (p0,p1,(1,3)) g, nm)
  where (g,nm,_) = insMapNode nodeMap0 p1 g0

(g2,nodeMap2) = (insMapEdge nm (p0,p2,(2,4)) g, nm)
  where (g,nm,_) = insMapNode nodeMap0 p2 g0

(g3,nodeMap3) = (insMapEdge nm (p1,p3,(2,3)) g, nm)
  where (g,nm,_) = insMapNode nodeMap1 p3 g1

(g4,nodeMap4) = (insMapEdge nm (p2,p4,(3,4)) g, nm)
  where (g,nm,_) = insMapNode nodeMap2 p4 g2

(g5,nodeMap5) = (insMapEdge nm (p2,p4,(1,2)) g, nm)
  where (g,nm,_) = insMapNode nodeMap4 p5 g4


-- all join pairs (assuming input list is sorted and uniq)
joinPairs []     = []
joinPairs [_]    = []
joinPairs (x:xs) = [(x,y) | y<-xs] ++ joinPairs xs

type M t = NodeMapM (Partition Int) (Int,Int) Gr t

-- join the partition containging i and the partition continaing j
addJoinFrom :: Partition Int -> (Int,Int) -> M (LNode (Partition Int))
addJoinFrom p (i,j) = do
  ln <- insMapNodeM p'
  insMapEdgeM (p,p',(i,j))
  return ln
  where p' = joinElems i j p

-- generate all possible partitions from p by a single join pair
-- and add them to the graph and nodemap
-- join pairs are generated from representative elem of each partition
addFrom :: Partition Int -> M [LNode (Partition Int)]
addFrom p = do
  lnodes <- mapM (addJoinFrom p) $ joinPairs (nub $ map (rep p) [0..maxVal])
  return $ nubBy (\x y -> fst x == fst y) lnodes

-- repeatedly apply addFrom to newly geneated partitions
-- until there are no more partitions to generate
addFromFix :: Partition Int -> M ()
addFromFix p = do
  lnodes <- addFrom p
  unless (null lnodes) $
    sequence_ [addFromFix p' | (_,p')<- lnodes]

instance GV.Labellable (Int,Int) where
  toLabelValue (i,j) = GV.toLabelValue (show i ++ "=" ++ show j)

instance GV.Labellable (Partition Int) where
  toLabelValue p = GV.toLabelValue (show $  toList <$> Partition.nontrivialSets p)

main :: IO ()
-- main = someFunc
main = do
  print p1
  print p1
  print p2
  print p3
  print p4
  print p5
  -- generate all substititions that equates variables in size 4 set
  -- where the elements are numberd as 0,1,2,3
  let (r,(nmap,g)) = run g0 (addFromFix p0)
  print r
  print nmap
  print g
  GV.preview g
-}
