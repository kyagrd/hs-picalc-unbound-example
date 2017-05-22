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

%if figureOpenLTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{figure}\small
\begin{code}
module OpenLTS where
import PiCalc; import Control.Applicative; import Control.Monad
import Data.Partition hiding (empty)
import Unbound.LocallyNameless hiding (empty, rep, GT)
import Data.Map.Strict (fromList, (!))

type EqC = [(Nm,Nm)]
infixr 5 .: {-"\;"-}; {-"\;"-} (.:) :: (Nm,Nm) -> EqC -> EqC
(x,y) .: sigma = case compare x y of  LT -> [(x,y)] .++ sigma
                                      EQ -> sigma
                                      GT -> [(y,x)] .++ sigma
infixr 5 .++ {-"\;"-}; {-"\;"-} (.++) :: EqC -> EqC -> EqC; {-"\;"-} (.++) = union

type Ctx = [Quan]
data Quan = All Nm | Nab Nm deriving (Eq, Ord, Show)
quan2nm :: Quan -> Nm; {-"\,"-} quan2nm (All x)  = x; {-"\,"-} quan2nm (Nab x)  = x

respects :: EqC -> Ctx -> Bool
respects sigma nctx = all (\n -> rep part n == n) [n2i x | Nab x <- nctx]
  where (part, (n2i, _)) = mkPartitionFromEqC nctx sigma

subs :: Subst Tm b => Ctx -> EqC -> b -> b
subs nctx sigma = foldr (.) id [subst x ((Var{-"\!"-}y)) | (x,y)<-sigma']
  where  sigma' = [(i2n i, i2n $ rep part i) | i<-[0..maxVal]]
         (part, (n2i, i2n)) = mkPartitionFromEqC nctx sigma
         maxVal = length nctx - 1

mkPartitionFromEqC ::  Ctx -> EqC ->
                         (Partition Int, (Nm -> Int, Int -> Nm))
mkPartitionFromEqC nctx sigma = (part, (n2i, i2n))
  where
    part =  foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- sigma]
               discrete
    i2n i = revns !! i
    n2i x = n2iMap ! x
    revns = reverse (quan2nm <$> nctx)
    n2iMap = fromList $ zip revns [0..maxVal]
    maxVal = length nctx - 1
\end{code}
\vspace*{-3.5ex}
\caption{Preamble of the |OpenLTS| module including type definitions and
helper functions for defining symbolic transition steps in Figure~\ref{fig:OpenLTS}.}
\label{fig:figureOpenLTS}
\vspace*{-1ex}
\end{figure}
%else %% figureOpenLTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\begin{figure}\small
\savecolumns
\begin{code}
-- preamble of this |OpenLTS| module is on Figure~\ref{fig:figureOpenLTS}

one :: (Fresh m, Alternative m) => Ctx -> Pr -> m (EqC,(Act,Pr))
one nctx  (Out x y p)   = return ([], (Up x y, p))
one nctx  (TauP p)      = return ([], (Tau, p))
one nctx  (Match (Var x) (Var y) p)  | x == y                   = one nctx p
                                     | [(x,y)] `respects` nctx  =
                                           do  (sigma, r) <- one nctx p
                                               let sigma' = (x,y) .: sigma
                                               guard $ sigma' `respects` nctx
                                               return (sigma', r)
one nctx  (Plus p q) = one nctx p <|> one nctx q
one nctx  (Par p q)
  =    do  (sigma,(l,p')) <- one nctx p; {-"~$~$"-} return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one nctx q; {-"~$~$"-} return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- oneb nctx p; {-"~$~$"-} (sigma_q,(lq,bq)) <- oneb nctx q
           case (lp, lq) of            {-"\quad\!\!"-} -- close
             (DnB(Var x),UpB(Var x'))  -> do  (y, q', p') <-  unbind2' bq bp
                                              let sigma' = (x,x') .: sigma_p .++ sigma_q
                                              guard $ sigma' `respects` nctx
                                              return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB(Var x'),DnB(Var x))  ->  {-"\ldots"-} -- omitted (close)
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                                          do  (y, p', q') <- unbind2' bp bq
                                              let sigma' = (x,x') .: sigma_p .++ sigma_q
                                              guard $ sigma' `respects` nctx
                                              return (sigma', (Tau, Nu(y.\Par p' q')))
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
             _                         -> empty
  <|>  do  (sigma_p, (Up (Var x) v, p')) <- one nctx p
           (sigma_q, (DnB (Var x'), bq)) <- oneb nctx q; {-""-} (y, q') <- unbind bq
           let sigma' = (x,x') .: sigma_p .++ sigma_q
           guard $ sigma' `respects` nctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  {-"\ldots"-} -- do block symmetric to above omitted (interaction)
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
       do  (sigma_p, (DnB (Var x'), (y,  p')))   <- oneb'  nctx p
           (sigma_q, (Up (Var x) v,     q'))    <- one    nctx q
           let sigma' = (x,x') .: sigma_p .++ sigma_q
           guard $ sigma' `respects` nctx
           return (sigma', (Tau, Par (subst y v p') q'))
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
one nctx (Nu b) = do  (x,p) <- unbind b;              let nctx' = Nab x : nctx
                      (sigma,(l,p')) <- one nctx' p;  let sigmaSubs = subs nctx' sigma
                      case l of  Up (Var x') (Var y)  | x == sigmaSubs x'  -> empty
                                                      | x == sigmaSubs y   -> empty
                                 _                    -> return (sigma, (l, Nu(x.\p')))
one _    _      = empty

oneb :: (Fresh m, Alternative m) => Ctx -> Pr -> m (EqC,(ActB, PrB))
oneb nctx (In x p) = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)  | x == y                   = oneb nctx p
                                     | [(x,y)] `respects` nctx  = {-"\ldots"-} -- omitted
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                                           do  (sigma, r) <- oneb nctx p
                                               let sigma' = (x,y) .: sigma
                                               guard $ sigma' `respects` nctx
                                               return (sigma', r)
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
oneb nctx (Plus p q) = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q) = {-"\ldots"-} -- omitted 
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
       do (sigma,(l,(x,p'))) <- oneb' nctx p; {-"~$~$"-} return (sigma,(l, x.\Par p' q))
  <|>  do (sigma,(l,(x,q'))) <- oneb' nctx q; {-"~$~$"-} return (sigma,(l, x.\Par p q'))
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
%%% \savecolumns
\begin{code}
oneb nctx (Nu b)  =    do  (x,p) <- unbind b;                    let nctx' = Nab x : nctx
                           (sigma,(l,(y,p'))) <- oneb' nctx' p;  let sigmaSubs = subs nctx' sigma
                           case l of  UpB (Var x')  | x == sigmaSubs x' -> empty
                                      DnB (Var x')  | x == sigmaSubs x' -> empty
                                      _             -> return (sigma, (l, y.\Nu (x.\p')))
                  <|>  do  (x,p) <- unbind b;                          let nctx' = Nab x : nctx
                           (sigma,(Up y (Var x'),p')) <- one nctx' p;  let sigmaSubs = subs nctx' sigma
                           guard $ x == sigmaSubs x' && Var x /= sigmaSubs y
                           return (sigma, (UpB y, x.\p')) -- open
oneb _    _ = empty

oneb' nctx p = do (sigma,(l,b)) <- oneb nctx p; r <- unbind b; return (sigma,(l,r))
\end{code}
\vspace*{-3.5ex}
\caption{Symbolic labeled transition semantics.}
\label{fig:OpenLTS}
\end{figure}


\subsection{Labeled Transition Steps over Possible Worlds}
\label{sec:lts:open}
The key idea behind the symbolic transition is that it is not worth considering
every single differences between worlds. For example, consider the process
|p1 `Par` ... `Par` p_n `Par` {-"\,"-} Match y z {-"\!"-}tau|
where |p_i = Out (V{-"\!"-}x_i) (V{-"\!"-}x_i) Null| for each |i`elem`[1..n]|.
The only difference that matters is whether |y| and |z| are unified in another world
so that it can make a |Tau|-step, which were not possible in the current world.
Other details such as whether |x_i| and |y|, |x_i| and |z|, or |x_j| and |x_k|
unifies are irrelevant.

A symbolic transition step collects necessary conditions, which are equality
constraints over names in our case, for making further steps in possible worlds
and keeps track of those constraints. Here is a run of a symbolic transition step
for the same example we ran with the fixed world version:\vspace*{-.5ex}
\begin{center}\small
\vspace*{-.5ex}
\begin{spec}
{-"\texttt{*Main> }"-} let p = Out{-"\!"-}(Var{-"\!"-}x)(Var{-"\!"-}x){-"\!"-}Null `Par` Out{-"\!"-}(Var{-"\!"-}y){-"\!"-}(Var{-"\!"-}y){-"\!"-}Null `Par` In{-"\!"-}(Var{-"\!"-}z){-"\!"-}(w.\Null)
{-"\texttt{*Main> }"-} mapM_ pp . runFreshMT $ OpenLTS.one [All{-"\!"-}z,{-"\!"-}All{-"\!"-}y,{-"\!"-}All{-"\!"-}x] p
([], (Up (Var x) (Var x), (Null `Par` {-"\,"-}(Out (Var y) (Var y) Null)) `Par` {-"\,"-}(In (Var z) (w.\Null))))
([], (Up (Var y) (Var x), ((Out (Var x) (Var y) Null) `Par` Null) `Par` {-"\,"-}(In (Var z) (w.\Null))))
{-"{\color{ACMDarkBlue}"-}([(x, z)], (Tau, (Null `Par` {-"\,"-}(Out (Var y) (Var y) Null)) `Par` Null)){-"}"-}
{-"{\color{ACMDarkBlue}"-}([(y, z)], (Tau, ((Out (Var x) (Var x) Null) `Par` Null) `Par` Null)){-"}"-}
{-"\texttt{*Main> }"-} mapM_ pp . runFreshMT $ OpenLTS.oneb [All{-"\!"-}z,{-"\!"-}All{-"\!"-}y,{-"\!"-}All{-"\!"-}x] p
([], (DnB (Var z), y.\ (((Out (Var x) (Var x) Null) `Par` {-"\,"-}(Out (Var y) (Var y) Null)) `Par` Null)))
\end{spec}
\vspace*{-3.5ex}
\end{center}
Two more interactions steps are possible: one where |x| and |z| are unified
and the other where |y| and |z| are unified.

The return types of |one| and |oneb| in Figure~\ref{fig:OpenLTS} reflect such
characteristics of symbolic transition. For instance, |one| returns
the equality constraint (|EqC|) along with the transition label (|Act|) and
the process (|Pr|). Another difference from the fixed world version is that
there is an additional context (|Ctx|) argument. The definitions of |EqC|
and |Ctx| are provided in Figure~\ref{fig:figureOpenLTS} along with related
helper functions. As a naming convention, we use |sigma| for equality constraints
and |nctx| for contexts. We follow through the definitions
in Figure~\ref{fig:figureOpenLTS} explaining how they are used
in the implementation symbolic transition steps in Figure~\ref{fig:OpenLTS}
while pointing out the differences from the fixed world version
in Figure~\ref{fig:IdSubLTS} laid out side-by-side.

\input{FigOpenLTS}

An equality constraint (|EqC|) is conceptually a set of name pairs represented
as a list. Basic operations over |EqC| are single element insertion (|.:|) and
union (|.++|). These operations are used on the necessary constraints 
for the additional steps, which were not possible in the current world.
Such additional steps may occur in match-prefixes, closing of scope extrusions,
and interaction steps.

A context (|Ctx|) is a list of either universally (|All|\,) or nabla (|Nab|\,) 
quantified names (|Quan|). We assume that names in a context must be distinct
(i.e., no  duplicates). When using the symbolic transition step (|one nctx p|),
we assume that |p| is closed by |nctx|, that is, $|(fv p)|\subset|(quan2nm<$>nctx)|$.
Similarly, for (|oneb nctx b|), we assume that |b| is closed by |nctx|.

Quantified names in a context appear in reversed order from how we usually
write on paper as a mathematical notation. That is, $\forall x,\!\nabla y,\!\forall z,...$
would correspond to |[All{-"\!"-}z,Nab{-"\!"-}y,All{-"\!"-}x]|.
This reversal of layout is typical for list representation of contexts
where the most recently introduced name is added to the head of the list.
Nabla quantified names must be fresh from all previously known names.
Hence, |y| may be unified with |z| but never with |x|. A substitution
|sigma `respects` nctx| when it obeys such nabla restrictions imposed by |nctx|.
Otherwise, i.e., |not(sigma `respects` nctx)|, it is an impossible world,
therefore, discarded by the |guard|s involving the |respect| predicate
in Figure~\ref{fig:OpenLTS}. These are additional |guard|s that were not
present in the fixed world setting.

We use the helper function |subs| to build a substitution function
(|sigmaSubs :: Subst Tm a => a->a|) from the context (|nctx|) and
equality constraints (|sigma|). The substitution function (|sigmaSubs|)
is used for testing name equivalence under the possible world given by |sigma|
in the transition steps for the restricted process (|Nu(x.\p)|).
The name (in)equality test for the restricted process in Figure~\ref{fig:IdSubLTS}
are now tested as (in)equality modulo substitution in Figure~\ref{fig:OpenLTS}.
For instance, the equality tests against the restricted name (|x|) such as
|x == x'| and |V{-"\!"-}x /= y| for the restricted process in Figure~\ref{fig:IdSubLTS}
are replaced by |x == sigmaSubs{-"\!"-}x'| and |V{-"\!"-}x /= sigmaSubs{-"\!"-}y|
in Figure~\ref{fig:OpenLTS}.
We need not apply |sigmaSubs| to the restricted name |x|, although
it would be harmless, because of our particular scheme for computing substitutions
using the helper function |mkPartitionFromEqC|, which is also used in
the definition of the |respects| predicate discussed earlier.

\subsection{Substitution modeled as Set Partitions}
\label{sec:lts:partition}
In |mkPartitionFromEqC|, we map names in |nctx| to inegers in decreasing order
so that more recently introduced names maps to larger values. For example,
consider |nctx = [All{-"\!"-}z,Nab{-"\!"-}y,All{-"\!"-}x]|,
which represents the context $\forall x,\!\nabla y,\!\forall z,...$
where |x| is mapped to 0, |y| to 1, and |z| to 2.
We model substitutions as integer set partitions using the \textsf{data-partition} library
and unification by its join operation (|joinElems|), which merges equivalence classes of
the joining elements (a.k.a., union-find algorithm). 
%{ %%%%
%format part1 = part"_1"
%format part2 = part"_2"
Consider the substitution described by |[(y,z)]|, which respects |nctx|,
modeled by the partition $|part1| = [[0],[1,2]]$. Also, consider |[(x,y)]|,
which does not respect |nctx|, modeled by $|part2| = [[0,1],[2]]$. %\footnote{These are merely
%	illustrative notations; not actual Haskell code.}
The representative of an equivalence class defined to be the minimal value.
Then, we can decide whether a partition models a respectful substitution by
examining |(rep part n)::Int| for every |n| that is mapped from a nabla name.
For instance, 1 from |y| in our example. In the first partition,
|rep part1 1 == 1| is the same as the nabla mapped value.
In the second partition, on the other hand, |rep part2 1 == 0|
is different from the nabla mapped value.
This exactly captures the idea that a nabla quantified name only unifies with
the names introduced later (larger values)
but not with names introduced earlier (smaller values).
%} %%%%%


%endif %% figureOpenLTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

