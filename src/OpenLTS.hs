{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
module OpenLTS where

import           Control.Applicative
import qualified Data.Map.Strict         as Map
import           Data.Partition          hiding (empty)
import qualified Data.Set                as Set
import           PiCalc
import           Unbound.LocallyNameless hiding (bind, empty, fresh, join, rep)
import qualified Unbound.LocallyNameless as LN

{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

-- TOOD can nctx and unification constraint collection
-- packaged as a set of monad transformer layers?

data Quan = All NameTm | Nab NameTm deriving (Eq, Ord, Show)

q2n (All x) = x
q2n (Nab x) = x

-- names in nctx must be distinct (i.e., no  duplicates)
one nctx (Out x y p)   = return ([], (Up x y, p))
one nctx (TauP p)      = return ([], (Tau, p))
one nctx (Match (Var x) (Var y) p) = do (s, r) <- one nctx p
                                        let s' = if x==y then s else (x,y):s
                                        if s' `respects` nctx
                                          then return (s', r)
                                          else empty
one nctx (Plus p q) = one nctx p <|> one nctx q
one nctx (Par p q)
   = do { (s,(l,p')) <- one nctx p; return (s,(l,Par p' q)) }
 <|> do { (s,(l,q')) <- one nctx q; return (s,(l,Par p q')) }
 <|> do (sp,(lp,bp)) <- oneb nctx p
        (sq,(lq,bq)) <- oneb nctx q
        case (lp, lq) of
          (DnB (Var x), UpB (Var y))
            -> do (w, p') <- unbind bp
                  (v, q') <- unbind bq
                  let p'' = subst w (Var v) p'
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s' `respects` nctx
                    then return (s', (Tau, Nu(v.\Par p'' q'))) -- close
                    else empty
          (UpB (Var x), DnB (Var y))
            -> do (v, p') <- unbind bp
                  (w, q') <- unbind bq
                  let q'' = subst w (Var v) q'
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s' `respects` nctx
                    then return (s', (Tau, Nu(v.\Par p' q''))) -- close
                    else empty
          _ -> empty
 <|> do (sp,(lp,bp)) <- oneb nctx p
        (sq,(lq,q')) <- one nctx q
        case (lp, lq) of
          (DnB (Var x), Up (Var y) v)
            -> do (w, p') <- unbind bp
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s' `respects` nctx
                    then return (s', (Tau, Par (subst w v p') q')) -- comm
                    else empty
          _ -> empty
 <|> do (sp,(lp, p')) <- one nctx p
        (sq,(lq, bq)) <- oneb nctx q
        case (lp, lq) of
          (Up (Var y) v, DnB (Var x))
            -> do (w, q') <- unbind bq
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s' `respects` nctx
                    then return (s', (Tau, Par p' (subst w v q'))) -- comm
                    else empty
          _ -> empty
one nctx (Nu b) = do (x,p) <- unbind b
                     (s,(l,p')) <- one (Nab x : nctx) p
                     return (s, (l, Nu(x.\p')))
one _    _ = empty

oneb nctx (In x p) = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)
     | x == y = oneb nctx p
     | otherwise = do { (s,r) <- oneb nctx p'; return ((x,y):s,r) }
                 where p' = subst x (Var y) p
oneb nctx (Plus p q) = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q)
   = do { (s,(l,b')) <- oneb nctx p; (x,p') <- unbind b'; return (s,(l, x.\Par p' q)) }
 <|> do { (s,(l,b')) <- oneb nctx q; (x,q') <- unbind b'; return (s,(l, x.\Par p q')) }
oneb nctx (Nu b)
   = do (x,p) <- unbind b
        (s,(l,b')) <- oneb (Nab x : nctx) p
        (y,p') <- unbind b'
        return (s, (l,  y.\Nu(x.\p'))) -- restriction
 <|> do (x,p) <- unbind b
        (s,(l,p')) <- one (Nab x : nctx) p
        case l of
          Up y x' | Var x == x' -> return (s, (UpB y, x.\p')) -- open
          _       -> empty
oneb _    _ = empty

-- nabla consistency check
respects s nctx = all (\n -> rep p n == n) nabs
  where
    nabs = [n2i x | Nab x <- nctx] -- index of nabla variables
    p = foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- s] p0
    i2n i = revns !! i
    n2i x = n2iMap Map.! x -- error if mapping from x not found
    n2iMap = Map.fromList $ zip revns [0..maxVal]
    revns = reverse $ map q2n nctx :: [NameTm]
    maxVal = length revns - 1 :: Int
    p0 = fromDisjointSets (fmap Set.singleton [0..maxVal]) :: Partition Int

{- Map names to ints in a decreasing manner,
  that is, from nctx :: [NameTm] to [n-1,...,0] :: Int.
The numbering is in reverse order since the most recnelty introduced variable
is at the head of nctx and the outermost at the last. Also map the s to
pairs of ints following the same mapping scheme. Then we can apply "join"
repeatedly for each pair of ints to the all-singleton partition, that is,
[[0],[1],...,[n-1]]. After joining, the "rep" value of each nabla variable
must be itself, being the least element of its equivalence class. Otherwise,
the nabla restriction has been violated because it means that there has been
an attempt to unify a nabla varible with another variable introduced before.
-}
