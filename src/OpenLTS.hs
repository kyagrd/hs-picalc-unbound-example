{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
module OpenLTS where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
import           Data.Maybe
import           PiCalc                           hiding (one, oneb)
import           Unbound.LocallyNameless          hiding (empty, fresh, join)
import qualified Unbound.LocallyNameless          as LN


{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

-- TOOD can nctx and unification constraint collection
-- packaged as a set of monad transformer layers?

data Quan = All NameTm | Nab NameTm deriving (Eq, Ord, Show)

one nctx (Out x y p)   = return ([], (Up x y, p))
one nctx (TauP p)      = return ([], (Tau, p))
one nctx (Match (Var x) (Var y) p) = do (s, r) <- one nctx p
                                        let s' = if x==y then s else (x,y):s
                                        return (s', r)
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
                    then return (s', (Tau, Nu (bind v $ Par p'' q'))) -- close
                    else empty
          (UpB (Var x), DnB (Var y))
            -> do (v, p') <- unbind bp
                  (w, q') <- unbind bq
                  let q'' = subst w (Var v) q'
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s `respects` nctx
                    then return (s', (Tau, Nu (bind v $ Par p' q''))) -- close
                    else empty
          _ -> empty
 <|> do (sp,(lp,bp)) <- oneb nctx p
        (sq,(lq,q')) <- one nctx q
        case (lp, lq) of
          (DnB (Var x), Up (Var y) v)
            -> do (w, p') <- unbind bp
                  let s  = sp `union` sq
                      s' = if x==y then s else (x,y):s
                  if s `respects` nctx
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
                  return (s', (Tau, Par p' (subst w v q'))) -- comm
          _ -> empty
one nctx (Nu b) = do (x,p) <- unbind b
                     (s,(l,p')) <- one (Nab x : nctx) p
                     return (s, (l, Nu (bind x p')))
one _    _ = empty

oneb nctx (In x p)      = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)
     | x == y = oneb nctx p
     | otherwise = do { (s,r) <- oneb nctx p'; return ((x,y):s,r) }
                 where p' = subst x (Var y) p
oneb nctx (Plus p q)    = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q)
   = do { (s,(l,b')) <- oneb nctx p; (x,p') <- unbind b'; return (s,(l,bind x $ Par p' q)) }
 <|> do { (s,(l,b')) <- oneb nctx q; (x,q') <- unbind b'; return (s,(l,bind x $ Par p q')) }
oneb nctx (Nu b)
   = do (x,p) <- unbind b
        (s,(l,b')) <- oneb (Nab x : nctx) p
        (y,p') <- unbind b'
        return (s, (l, bind y $ Nu (bind x p'))) -- restriction
 <|> do (x,p) <- unbind b
        (s,(l,p')) <- one (Nab x : nctx) p
        case l of
          Up y x' | Var x == x' -> return (s, (UpB y, bind x p')) -- open
          _       -> empty
oneb _    _ = empty

-- nabla consistency check
respects s nctx = True -- TODO
{- Map names to ints in a decreasing manner,
that is nctx :: [NameTm] to [n-1,...,0] :: Int since the most recnelty
introduced variable is at the head and the outermost the last. Also map
the s to pairs of ints by the same mapping scheme. Then we can apply "join"
repeatedly for each pair of ints to the all-singleton partition, that is,
[[0],[1],...,[n-1]]. The "rep" value of nabla must always be itself, being
the least element of its equivalence class. Otherwise, the nabla restriction
has been violated because it means that there has been an attempt to unify
a nabla varible.
-}
