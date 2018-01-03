{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module IdSubLTS where
import           Control.Applicative
import           Control.Monad
import qualified Data.Set                as Set
import           PiCalc
import           Unbound.LocallyNameless hiding (empty)

type NmSet = Set.Set Nm

one :: (Fresh m, Alternative m) => NmSet -> Pr -> m (Act, Pr)
one _ (Out x y p)    = return (Up x y, p)
one _ (TauP p)       = return (Tau, p)
one ns (Match x y p)  | x == y = one ns p
one ns (Diff (Var x) (Var y) p)
  | (Set.member x ns || Set.member y ns) && x /= y   = one ns p
one ns (Plus p q) = one ns p <|> one ns q
one ns (Par p q)
  =    do  (l, p') <- one ns p;  return (l, Par p' q)
  <|>  do  (l, q') <- one ns q;  return (l, Par p q')
  <|>  do  (lp, bp) <- oneb ns p;  (lq, bq) <- oneb ns q
           case (lp, lq) of  (UpB x,DnB x') | x == x'           -- close
                                            -> do  (y, p', q') <- unbind2' bp bq
                                                   return (Tau, Nu(y.\Par p' q'))
                             (DnB x',UpB x) | x' == x           -- close
                                            -> do  (y, q', p') <- unbind2' bq bp
                                                   return (Tau, Nu(y.\Par p' q'))
                             _              -> empty
  <|>  do  (Up x v, p') <- one ns p;  (DnB x', (y,q')) <- oneb' ns q
           guard $ x == x'
           return (Tau, Par p' (subst y v q'))  -- interaction
  <|>  do  (DnB x', (y,p')) <- oneb' ns p;  (Up x v, q') <- one ns q
           guard $ x == x'
           return (Tau, Par (subst y v p') q')  -- interaction
one ns (Nu b)  = do  (x,p) <- unbind b
                     (l,p') <- one (Set.insert x ns) p
                     case l of  Up (Var x') (Var y)  | x == x'  -> empty
                                                     | x == y   -> empty
                                _                    -> return (l, Nu (x.\p'))
one _ _       = empty
-- TODO mismatch

oneb :: (Fresh m, Alternative m) => NmSet -> Pr -> m (ActB, PrB)
oneb _ (In x p)     = return (DnB x, p)
oneb ns (Match x y p) | x == y = oneb ns p
oneb ns (Diff (Var x) (Var y) p)
  | (Set.member x ns || Set.member y ns) && x /= y   = oneb ns p
oneb ns (Plus p q)  = oneb ns p <|> oneb ns q
oneb ns (Par p q)   =     do  (l,(x,p')) <- oneb' ns p;  return (l, x.\Par p' q)
                    <|>   do  (l,(x,q')) <- oneb' ns q;  return (l, x.\Par p q')
oneb ns (Nu b)      =     do  (x,p) <- unbind b
                              (l,(y,p')) <- oneb' (Set.insert x ns) p
                              case l of  UpB (Var x')   | x == x' -> empty
                                         DnB (Var x')   | x == x' -> empty
                                         _              -> return (l, y.\Nu (x.\p'))
                    <|>   do  (x,p) <- unbind b
                              (Up y (Var x'),p') <- one ns p
                              guard $ x == x' && Var x /= y
                              return (UpB y, x.\p')  -- open
oneb _ _           = empty

oneb' ns p = do (l,b) <- oneb ns p; r <- unbind b; return (l,r)

{-
  p
% Finite pi-calculus specification in lambda-Prolog
% A specification of the late transition system for the finite pi calculus.

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
