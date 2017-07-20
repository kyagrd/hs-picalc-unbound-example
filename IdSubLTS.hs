{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module IdSubLTS where
import           Control.Applicative
import           Control.Monad
import           PiCalc
import           Unbound.LocallyNameless hiding (empty)
{-# ANN module "HLint: ignore Use mappend" #-}

one :: (Fresh m, Alternative m) => Knw -> Pr -> m (Act, Pr)
one _   (Out x y p)    = return (Up x y, p)
one _   (TauP p)       = return (Tau, p)
one knw (Match x y p)  | x == y = one knw p
one knw (Let b)
  = do ((pat,Embed t), p) <- unbind b
       -- TODO check pat should not contain duplicat vars
       case (pat, t) of
         (V x, _) -> one knw (subst x t p)
         (D "pair" [pat1, pat2], D "pair" [t1, t2])
            -> one knw $ Let (bind (pat1,embed t1) $ Let (bind (pat2,embed t2) p))
         (D "pair" [_, _], _) -> empty
         (D "enc" [pat1, pat2], D "enc" [t1, t2]) | syn knw t2
            -> one knw $ Let (bind (pat2, embed t2) $ Let (bind (pat1, embed t1) p))
         (D "enc" [_, _], _) -> empty
         _ -> fail $ "unsupported pattern " ++ show pat
one knw (Plus p q) = one knw p <|> one knw q
one knw (Par p q)
  =    do  (l, p') <- one knw p;  return (l, Par p' q)
  <|>  do  (l, q') <- one knw q;  return (l, Par p q')
  <|>  do  (lp, bp) <- oneb knw p;  (lq, bq) <- oneb knw q
           case (lp, lq) of  (UpB x,DnB x') | x == x'           -- close
                                            -> do  (y, p', q') <- unbind2' bp bq
                                                   return (Tau, Nu(y.\Par p' q'))
                             (DnB x',UpB x) | x' == x           -- close
                                            -> do  (y, q', p') <- unbind2' bq bp
                                                   return (Tau, Nu(y.\Par p' q'))
                             _              -> empty
  <|>  do  (Up x v, p') <- one knw p;  (DnB x', (y,q')) <- oneb' knw q
           guard $ x == x'
           return (Tau, Par p' (subst y v q'))  -- interaction
  <|>  do  (DnB x', (y,p')) <- oneb' knw p;  (Up x v, q') <- one knw q
           guard $ x == x'
           return (Tau, Par (subst y v p') q')  -- interaction
one knw (Nu b) = do  (x,p) <- unbind b
                     (l,p') <- one knw p
                     case l of  Up _ _ | x `elem` (fv l :: [Nm]) -> empty
                                _      -> return (l, Nu (x.\p'))
one _   _  = empty

oneb :: (Fresh m, Alternative m) => Knw -> Pr -> m (ActB, PrB)
oneb _   (In x p)      = return (DnB x, p)
oneb knw (Match x y p) | x == y = oneb knw p
oneb knw (Let b)
  = do ((pat,Embed t), p) <- unbind b
       -- TODO check pat should not contain duplicat vars
       case (pat, t) of
         (V x, _) -> oneb knw (subst x t p)
         (D "pair" [pat1, pat2], D "pair" [t1, t2])
            -> oneb knw $ Let (bind (pat1,embed t1) $ Let (bind (pat2,embed t2) p))
         (D "pair" [_, _], _) -> empty
         (D "enc" [pat1, pat2], D "enc" [t1, t2]) | syn knw t2
            -> oneb knw $ Let (bind (pat2, embed t2) $ Let (bind (pat1, embed t1) p))
         (D "enc" [_, _], _) -> empty
         _ -> fail $ "unsupported pattern " ++ show pat
oneb knw (Plus p q)  = oneb knw p <|> oneb knw q
oneb knw (Par p q)   =     do  (l,(x,p')) <- oneb' knw p;  return (l, x.\Par p' q)
                     <|>   do  (l,(x,q')) <- oneb' knw q;  return (l, x.\Par p q')
oneb knw (Nu b)      =     do  (x,p) <- unbind b
                               (l,(y,p')) <- oneb' knw p
                               case l of  UpB (V x') | x == x' -> empty
                                          DnB (V x') | x == x' -> empty
                                          _          -> return (l, y.\Nu (x.\p'))
                     <|>   do  (x,p) <- unbind b
                               (Up y t2,p') <- one knw p
                               guard $ x `elem` (fv t2 :: [Nm]) && V x /= y
                               return (UpB y, x.\p')  -- open
oneb _   _           = empty

oneb' knw p = do (l,b) <- oneb knw p; r <- unbind b; return (l,r)

{-
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
