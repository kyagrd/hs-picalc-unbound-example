%include mylhs2tex.lhs
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%

\subsection{Labeled Transition Steps in a Fixed World}
\label{sec:lts:ids}
Figure~\ref{fig:IdSubLTS} is a straightforward transcription of 
the transition rules (including the omitted symmetric cases)
from Figure~\ref{fig:lts} where \,|(l,p) <- one p|\, and \,|(l,b) <- oneb p|\,
correspond to free and bound steps \,$p\xone{l}p'$\, and \,$p\xoneb{l}b$\,
respectively.

The type signatures of |one| and |oneb| indicates that freshness of names
and nondeterminism are handled by a monadic computation that returns
a pair of a (bound) action and a (bound) process. In this paper, you may
simply consider |one| and |oneb| as returning a list of all possible pairs.
For example, we can compute all the three possible next steps from the process
{\small|Out (Var x) (Var x) Null `Par` Out (Var w) (Var w) Null `Par` In (Var z) (y.\Null)|}
using ghci as follows:\vspace*{-.5ex}\footnote{|pp :: Pretty a => a -> IO ()| is
	our pretty printing utility function, which is not going to be discussed
	in this paper. It is for printing out a more readable format the default
	derived show instances provided by the unbound library.}
\begin{center}\small
\vspace*{-.5ex}
\begin{spec}
{-"\texttt{*Main> :type }"-} runFreshMT . IdSubLTS.one 
runFreshMT . IdSubLTS.one :: MonadPlus m => Pr -> m (Act, Pr)
{-"\texttt{*Main> :type }"-} map id . runFreshMT . IdSubLTS.one 
map id . runFreshMT . IdSubLTS.one :: Pr -> [(Act, Pr)]
{-"\texttt{*Main> }"-} let p = Out{-"\!"-}(Var{-"\!"-}x)(Var{-"\!"-}x){-"\!"-}Null `Par` Out{-"\!"-}(Var{-"\!"-}y){-"\!"-}(Var{-"\!"-}y){-"\!"-}Null `Par` In{-"\!"-}(Var{-"\!"-}z){-"\!"-}(w.\Null)
{-"\texttt{*Main> }"-} mapM_ pp . runFreshMT . IdSubLTS.one $ p
(Up (Var x) (Var x),(Null `Par` Out (Var y) (Var y) Null) `Par` {-"\,"-}(In (Var z) (w.\Null)))
(Up (Var y) (Var y),(Out (Var x) (Var x) Null `Par` Null) `Par` {-"\,"-}(In (Var z) (w.\Null)))
{-"\texttt{*Main> }"-} mapM_ pp . runFreshMT . IdSubLTS.oneb $ p
(DnB (Var z),y.\ (((Out (Var x) (Var x) Null) `Par` {-"\,"-}(Out (Var y) (Var y) Null)) `Par` Null))
\end{spec}
\vspace*{-3.5ex}
\end{center}

In principle, the possible worlds semantics could be implemented using
|one| and |oneb| in this |IdSubLTS| module by brute force enumeration of
all substitutions over the free names in the process. For instance,
there are three free names (|x|,|y|,|z|) in the process (|p|) above.
Enumerating all substitutions over 3 names amounts to considering all
possible integer set partition of the 3 elements.
Let us establish a 1-to-1 mapping of |x| to 0, |y| to 1, and |z| to 2.
Then, a substitution that map |x| and |z| to the same value but |y| to
a different value corresponds to the partition [[0,2],[1]] where
0 and 2 belong to the same equivalence class. In such a world, there
is an additional possible step for |p| above, which is the interaction
between |Out (Var x) (Var x) Null| and |In (Var z) (y.\Null)| due to
the unification of |x| and |z|. More generally, we can generate
all possible partitions, starting from the distinct partition [[0],[1],[2]],
by continually joining a pair of elements from different equivalence classes
until all possible joining paths reaches [[0,1,2]] where all elements are joined.
Although this brute force approach is a terminating algorithm, the number of
partition sets grows too fast, exponential to the number of names \cite{Rota64bell}.

Since the original development of open bisimulation, \citet{Sangiorgi96acta}
was well aware that enumerating all possible worlds is intractable and
provided a more efficient set of transition rules, known as
the symbolic transition semantics. We implement another version of |one|
and |oneb| following the style of symbolic transition in the next subsection.
Nevertheless, |one| and |oneb| in this subsection are still used
in our implementation of open bisimulation, together with the symbolic version.
We will explain why we use both versions to implement open bisimulation
in Section~\ref{sec:bisim}.


\begin{figure}\small
\vspace*{2.7ex}
\begin{code}
module IdSubLTS where
import PiCalc
import Control.Applicative
import Control.Monad
import Unbound.LocallyNameless hiding (empty)

one :: (Fresh m, Alternative m) => Pr -> m (Act, Pr)
one (Out x y p)    = return (Up x y, p)
one (TauP p)       = return (Tau, p)
one (Match x y p)  | x == y = one p
one (Plus p q) = one p <|> one q
one (Par p q)
  =    do  (l, p') <- one p; {-"\;"-} return (l, Par p' q)
  <|>  do  (l, q') <- one q; {-"\;"-} return (l, Par p q')
  <|>  do  (lp, bp) <- oneb p; {-"\;"-} (lq, bq) <- oneb q
           case (lp, lq) of  (UpB x,DnB x') | x == x'           -- close
                                            -> do  (y, p', q') <- unbind2' bp bq
                                                   return (Tau, Nu(y.\Par p' q'))
                             (DnB x',UpB x) | x' == x           -- close
                                            -> do  (y, q', p') <- unbind2' bq bp
                                                   return (Tau, Nu(y.\Par p' q'))
                             _              -> empty
  <|>  do  (Up x v, p') <- one p; {-"\;"-} (DnB x', (y,q')) <- oneb' q
           guard $ x == x'
           return (Tau, Par p' (subst y v q'))  -- interaction
  <|>  do  (DnB x', (y,p')) <- oneb' p; {-"\;"-} (Up x v, q') <- one q
           guard $ x == x'
           return (Tau, Par (subst y v p') q')  -- interaction
one (Nu b)  = do  (x,p) <- unbind b
                  (l,p') <- one p
                  case l of  Up (Var x') (Var y)  | x == x'  -> empty
                                                  | x == y   -> empty
                             _                    -> return (l, Nu (x.\p'))
one _       = empty

oneb :: (Fresh m, Alternative m) => Pr -> m (ActB, PrB)
oneb (In x p)      = return (DnB x, p)
oneb (Match x y p) | x == y = oneb p
oneb (Plus p q)  = oneb p <|> oneb q
oneb (Par p q)   =     do  (l,(x,p')) <- oneb' p; {-"\;"-} return (l, x.\Par p' q) 
                 <|>   do  (l,(x,q')) <- oneb' q; {-"\;"-} return (l, x.\Par p q')
oneb (Nu b)      =     do  (x,p) <- unbind b
                           (l,(y,p')) <- oneb' p
                           case l of  UpB (Var x')   | x == x' -> empty
                                      DnB (Var x')   | x == x' -> empty
                                      _              -> return (l, y.\Nu (x.\p'))
                 <|>   do  (x,p) <- unbind b
                           (Up y (Var x'),p') <- one p
                           guard $ x == x' && Var x /= y
                           return (UpB y, x.\p')  -- open
oneb _           = empty

oneb' p = do (l,b) <- oneb p; {-"\;"-} r <- unbind b; {-"\;"-} return (l,r)
\end{code}
\vspace*{-3.5ex}
\caption{Labeled transition semantics within a fixed world.}
\label{fig:IdSubLTS}
\end{figure}


%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{verbatim}
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
\end{verbatim}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
