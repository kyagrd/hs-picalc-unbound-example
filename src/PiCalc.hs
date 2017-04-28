{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module PiCalc where

import           Control.Applicative
-- import           Control.Monad                    (unless)
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
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
 <|> do (x,p) <- unbind b
        (l,p') <- one p
        case l of Up y x' | Var x == x' -> return (UpB y, bind x p')  -- open
                  _       -> empty
oneb _ = empty

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
