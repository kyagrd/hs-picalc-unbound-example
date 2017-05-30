%include mylhs2tex.lhs

%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%

\begin{figure}\small
\begin{code}
module PiCalc where
import Unbound.LocallyNameless

type Nm = Name Tm
newtype Tm = Var Nm deriving (Eq, Ord, Show)

data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB | Match Tm Tm Pr
         | Plus Pr Pr | Par Pr Pr | Nu PrB {-"\hspace{4ex}"-} deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr
instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare

data Act   = Up Tm Tm  | Tau     deriving (Eq, Ord, Show)
data ActB  = UpB Tm    | DnB Tm  deriving (Eq, Ord, Show)

data Form  = FF | TT | Conj [Form] | Disj [Form]
           | Dia  Act Form  |  DiaB  ActB FormB   | DiaMatch [(Tm,Tm)] Form 
           | Box  Act Form  |  BoxB  ActB FormB   | BoxMatch [(Tm,Tm)] Form
           deriving (Eq,Ord,Show)
type FormB = Bind Nm Form
instance Eq FormB where (==) = aeqBinders
instance Ord FormB where compare = acompare

$(derive [''Tm, ''Act, ''ActB, ''Pr, ''Form])

instance Alpha Tm; {-""-}  instance Alpha Act; {-""-} instance Alpha ActB
instance Alpha Pr; {-""-}  instance Alpha Form

instance Subst Tm Tm where isvar (Var x) = Just (SubstName x)
instance Subst Tm Act; {-""-} instance Subst Tm ActB
instance Subst Tm Pr; {-""-} instance Subst Tm Form

infixr 1 .\ {-"\,"-};{-"\,"-} (.\) :: Alpha t => Nm -> t -> Bind Nm t {-"\,"-};{-"\,"-} (.\) = bind

x .= y = Match (Var x) (Var y) {-"\,"-};{-"~"-} inp = In . Var {-"\,"-};{-"~"-} out x y = Out(Var x)(Var y)
tau = TauP Null {-"\,"-};{-"\quad"-} tautau = TauP (TauP Null)

conj  = cn . filter(/=TT) where cn  [] = TT; cn  [f] = f; cn  fs = Conj fs
disj  = ds . filter(/=FF) where ds  [] = FF; ds  [f] = f; ds  fs = Disj fs

unbind2' b1 b2 = do  Just (x,p1,_,p2) <- unbind2 b1 b2
                     return (x,p1,p2)
\end{code}
\vspace*{-4ex}
\caption{Syntax of the $\pi$-calculus and the modal logic \OM.}
\label{fig:PiCalc}
\vspace*{-2.5ex}
\end{figure}

%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
(.+)  = Plus  ; {-""-}  infixl 6 .+
(.|)  = Par   ; {-""-} infixl 5 .|
o = Null
taup = TauP
nu = Nu
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%


\section{Syntax}
\label{sec:syntax}
In this section, we define the syntax for the $\pi$-calculus and
the modal logic, which characterizes open bisimilarity.
Haskell definitions of the syntax for both are provided
in the module |PiCalc| as illustrated in Figure~\ref{fig:PiCalc}.

% In general, $\pi$-calculus and its characterizing logic shares a common term
% structure, which represents either communication channels or values that
% are communicated through those channels. For instance, terms in some
% applied variants of $\pi$-calculi (e.g., \cite{Abadi97ccs,AbaFou01appi})
% are equipped with encryption primitives for modeling security protocols.
% Here, we consider a basic version where terms only consist of names,
% as in the original development of the $\pi$-calculus~\cite{Milner92picalcI,Milner92picalcII}.

Since we consider only the original version of the $\pi$-calculus
with name passing, terms (|Tm|) that can be sent through channel names consist
only of names. 
Processes (|Pr|) may contain bound names due to
value passing and name restriction. In the Haskell definition,
we define these name binding constructs with the generic binding
scheme (|Bind|) from the \textsf{unbound}~\cite{unbound11} library.
We can construct a bound process (|PrB|, i.e., |Bind Nm Pr|) by applying
the binding operator |(.\)| to a name (|Nm|) that may be used in
a process (|Pr|), i.e., |(x.\p)::PrB| given |x::Nm| and |p::Pr|.
Intuitively, our Haskell expression |(x.\p)| corresponds to
a lambda-term $(\lambda x.p)$. Similarly, we define name bindings
in the logic formulae (|Form|) with |FormB| defined as |Bind Nm Form|.
We get $\alpha$-equivalence and capture-avoiding substitutions over
processes and formulae almost for free, with a few lines of instance
declarations, thanks to the \textsf{unbound} library.

In addition to the binding operator |(.\)|, we define some utility functions:
(|.=|), |inp|, and |out| are wrappers to the data constructors of |Pr|,
for example, |out x y == Out (V x) (V y)|; |tau| and |tautau|
are shorthand names of example processes;
|conj| and |disj| are wrappers of |Conj| and |Disj| with
obvious simplifications, for example, |f == conj [TT,f]|; and
|undbind2'| is a wrapper to the library function |unbind2|, which unbinds two bound structures
by a common name, for example,\\
$\phantom{i}${\small|(x,out x x Null,out x x tau) <- unbind2 (x.\out x x Null) (y.\out y y tau)|}.
There is of course a more basic library function \textit{unbind} for a single bound structure,
which is formatted as |unbind| in this paper because it acts like an inverse of |(.\)|.

As a convention, we use Haskell names suffixed by {\textsc{b}} to emphasize
that those definitions are related to bound structures. Naming conventions
for the values of other data types in Figure~\ref{fig:PiCalc} are:
|x|, |y|, |z|, and |w| for both terms (|Tm|) and names (|Nm|);
|v| for terms (|Tm|);
|p| and |q| for processes (|Pr|); |b| for bound processes (|PrB|);
|a| and |l| for both free and bound actions (|Act| and |ActB|); and
|f| for formulae (|Form|).

In the following subsections, we explain further details of
the finite $\pi$-calculus (Section~\ref{sec:syntax:pi}) and 
the modal logic (Section~\ref{sec:syntax:om}) including
the intuitive meanings of their syntax.

\subsection{Finite $\pi$-Calculus}
\label{sec:syntax:pi}
\begin{figure*}
$\displaystyle 
\begin{matrix} \phantom{a} \\ |TauP p| \xone{|Tau|} |p| \end{matrix}  \qquad \quad
\begin{matrix} \phantom{a} \\ |Out x y p| \xone{|Up x y|} |p| \end{matrix} \qquad \quad
\begin{matrix} \phantom{a} \\ |In x b| \xoneb{|DnB x|} |b| \end{matrix} \qquad \quad
\frac{|p| \xone{a} |p'|}{|Match x x p| \xone{a} |p'|} \qquad \quad
\frac{|p| \xoneb{a_\textsc{b}} b}{|Plus p q| \xoneb{a_\textsc{b}} b} \qquad 
\frac{|p| \xone{a} |p'|}{|Plus p q| \xone{a} |p'|} \qquad
$
\\[.5ex]
\[
\frac{p \xone{a} p'}{|Par p q| \xone{a} |Par p' q|}
\qquad
\frac{p \xoneb{a_\textsc{b}} |(x.\p')|}{|Par p q| \xoneb{a_\textsc{b}} |(x.\Par p' q)|}
\qquad
\frac{|p| \xone{|Up x v|} |p'| \quad |q| \xoneb{|DnB x|} |(y.\q')|}{
      |Par p q| \xone{|Tau|} |Par p' (subst y v q')| }
\qquad
\frac{|p| \xoneb{|UpB x|} |(y.\p')| \quad |q| \xoneb{|DnB x|} |(y.\q')|}{
      |Par p q| \xone{|Tau|} |Nu(y.\Par p' q')| }{\quad\text{(close scope-ext)}}
\]
\[
\quad
\frac{|p| \xone{|a|} |p'|}{|Nu(x.\p)| \xone{|a|} |Nu(x.\p')|}{~~~ |x|\notin\textrm{fv}(a)}
\qquad
\frac{|p| \xoneb{a_\textsc{b}} |(y.\p')|}{|Nu(x.\p)| \xoneb{a_\textsc{b}} |(y.\Nu(x.\p'))|}{~~~ |x|\notin\textrm{fv}(a)}
\qquad
\frac{|p| \xone{|Up y (Var x)|} |p'|}{|Nu(x.\p)| \xoneb{|UpB y|} |(x.\p')|}{~~~ |y/=x|} \quad\text{(open scope-ext)}
\]
\vspace*{-1.5ex}
\caption{Labeled transition rules of the finite $\pi$-calculus (symmetric cases for |`Plus`| and  |`Par`| are omitted).}
\label{fig:lts}
\end{figure*}


A process (|Pr|) in the finite $\pi$-calculus is either
the |Null| process,
a $\tau$-prefixed process |(TauP p)|,
an input-prefixed process |(In x (y.\p))|,
an output-prefixed process |(Out x y p)|,
a parallel composition of processes |(Par p q)|,
a nondeterministic choice between processes |(Plus p q)|,
a name-restricted process |(Nu(x.\p))|, or
a match-prefixed process |(Match x y p)|.

The operational semantics of the finite $\pi$-calculus is given
in Figure~\ref{fig:lts}. Here we follow a style of
specification~\cite{McDowell96} of the $\pi$-calculus where the
continuation of an input or a bound output transition is
represented as an abstraction over processes. 

The process |Null| is a terminated process so that it will never make
any transitions.
%% Hence, there are no labeled transition rules from |Null|
%% in Figure~\ref{fig:lts}.
|(TauP p)| will make a (free) transition step evolving into |p|
labeled with (free) action |Tau::Act|, that is, $|TauP p|\xone{|Tau|}|p|$.
|(Out x y p)| will make a step evolving into |p| labeled with |Up x y::Act| and
produces a value |y| on channel |x|, which can be consumed by another process
expecting an input value on the same channel.

|(In x (y.\p))| can make a step evolving into |p| once an input value
is provided on channel |x|. When an input value |v::Tm|\, is provided
on the channel, at some point in time, the process consumes the value
and evolves to |(subst y v p)|, which is a process where |(Var y)|
inside |p| are substituted by |v|.
This concept of a conditional step described above can be understood as if
it steps to a bound process |(y.\p)::PrB|, waiting for an input value for |y|.
It is called a bound step ($\xoneb{a_\textsc{b}}$) in contrast to
the (free) step ($\xone{a}$) for the $\tau$-prefix case. Bound steps are
labeled by bound actions, which can viewed as partially applied actions.%%\footnote{%
%% The reason for defining a separate data type (|ActB|) for bound actions from
%% the data type (|Act|) for free actions is because functional languages like
%% Haskell do not generally support pattern matching against partially applied
%% data constructors.} For example, |UpB x::ActB| can be understood as
%% representing |Up x::Tm->Act|. Transition rules involving bounded output actions
%% (|UpB|) are soon to be explained in the context of the name-restricted process.

|(Match x y p)| behaves as |p| when |x| is same as |y|.
Otherwise, it cannot make any further steps.

|(Plus p q)| nondeterministically becomes either |p| or |q|, and 
take steps thereafter. Only the rules for choosing |p| are illustrated
in Figure~\ref{fig:lts} while the rules for choosing |q| are omitted.

|(Par p q)| has eight possible cases; modulo symmetry between |p| and |q|, four.
First, it may step to |(Par p' q)| with action |a| when |p| steps to |p'|
with the same action. Second, there is a bound step version of the first.
Third, the two parallel processes can interact when |p| steps to |p'| with
an output action |Up x v| and |q| steps to |(y.\q')| with an (bound) input
action |DnB x| on the same channel. This interaction step is labeled with |Tau|
and the process evolves into |(Par p (subst y v q'))|.
Forth {\small(close scope-ext)} is a bound interaction step similar to the third.
The differences from the third is that there is a bounded output (|UpB|)
instead of a free ouput (|Up|\;) and that the resulting process becomes
restricted with the name |x| from the output value |(V x)|.
The bound output ({\small(open scope-ext)}) is driven by 
name-restricted processes, as explained next.

|Nu(x.\p)| restricts actions of |p| involving the restricted name |x| from
being observed outside the scope restricted by |Nu|. For example, neither
|Nu{-"\!"-}(x.\Out{-"\!"-}(V{-"\!"-}x){-"\!"-}v{-"\hspace{-.2ex}"-}p)|
nor |Nu{-"\!"-}(x.\In{-"\!"-}(V{-"\!"-}x){-"\!"-}(y.\q))| can make
any further steps. However, communication over the restricted channel |(V{-"\!"-}x)|
is still possible as long as the restricted name |x| is not observable from outside.
For example, 
$ |Nu{-"\!"-}(x.\Par (Out (V{-"\!"-}x) v p) (In (V{-"\!"-}x) (y.\q)))|
  \xone{|Tau|} |Nu{-"\!"-}(x.\Par p (subst y v {-"\!"-}q))|. $
The last rule {\small(open scope-ext)} is the source of the bounded output when
the output over a non-restricted channel happens to be the restricted value
|(V{-"\!"-}x)|. This bound output is to be consumed by interacting with
another process waiting for an input on the same channel, according to
the rule {\small(close scope-ext)} mentioned above. For example, \vspace*{-.75ex}
{\small\setpremisesend{1pt}\setnamespace{1pt}
\[
 \inference[close]{\!\!\!\!\!\!\!\!
   \inference*[open]{|Out y (V{-"\!"-}x) p| \xone{|Up{-"\!"-}y{-"\!"-}(V{-"\!"-}x)|} |p|
    }{|Nu{-"\!"-}(x.\Out y (V{-"\!"-}x) p)| \xoneb{|UpB y|} |(x.\p)|}
   &
     |In y (z.\q)| \xoneb{|DnB y|} |(z.\q)|
 }{
  |Par (Nu{-"\!"-}(x.\{-"\uwave{"-}Out y{-"\!"-}(V{-"\!"-}x) p{-"}"-})) (In y (z.\q))| \xone{|Tau|}
  |Nu{-"\!"-}(x.\{-"\uwave{"-}Par p (subst z ((V{-"\!"-}x)) {-"\!"-}q){-"}"-})| }
\]\\[-2.5ex]}
Before the interaction step, the scope of restriction (marked by \uwave{wavy underline})
did not include the input process on the right-hand side of parallel composition.
After the step, the scope of restriction includes the right-hand side,
adjusting to include the restricted output |(V{-"\!"-}x)| extruded from
the original scope through the non-restricted channel |y|.
The rule {\small(open scope-ext)} together with
the rule {\small(close scope-ext)} descirbes
the feature known as \emph{scope extrusion} in the $\pi$-calculus.

The labeled transition rules of Figure~\ref{fig:lts} are implemented
as Haskell programs, which are to be discussed in Section~\ref{fig:lts}.

\subsection{Modal Logic \OM}
\label{sec:syntax:om}

An \OM\ formulae |f| describes a behavior pattern of processes.
$|p| \models |f|$, read as ``|p| satisfy |f|'' or ``|f| is satisfied by |p|'',
holds when the process |p| follows the behavior described by |f|.
Let $\mathcal{L}(p) = \{f \in |Form| \mid p \models f\}$,
the set of formulae satisfied by |p|.
We~\cite{AhnHorTiu17corr} recently established that $\mathcal{L}(p) \equiv \mathcal{L}(q)$
exactly coincides with $p \sim_o q$, that is, |p| and |q| are open bisimilar.
By contraposition, $\mathcal{L}(p) \not\equiv \mathcal{L}(q)$ whenever
$p \not\sim_o q$, that is, there must exists $f$ that satisfy one of
the two non-bisimilar processes but not the other. Such a formula is known as
a \emph{distinguishing formula}. This formula explains how two processes
behave differently so that it can serve as a certificate of non-bisimilarity
if we have an implementation to check satisfiability of |f| for
a given process, which we already do have \cite{AhnHorTiu17corr}.

An \OM\ formula (|Form|) is either the falsity (|FF|), the truth (|TT|),
a conjunction (|Conj fs|), a disjunction (|Disj fs|),
a dia-action (|Dia a f|),
a box-action (|Box a f|),
a bound dia-action (|DiaB a (x.\ f)|),
a bound box-action (|BoxB a (x.\ f)|),
a dia-match (|DiaMatch [(x_i,y_i)] f|), or
a box-match (|BoxMatch [(x_i,y_i)] f|).\footnote{Standard notations
	in the literature (and also in Figure~\ref{fig:example})
	are $[a]f$ and $\langle a \rangle f$ for box- and dia-actions;
	and, $[x=y]f$ and $\langle x=y \rangle f$ for box- and dia-matches.
	The notations used for bound actions may vary between different notions of
	bisimilarities discussed in Section~\ref{sec:relwork:logic}. }
Intuitive meanings of these formulae can be best understood by 
the \emph{possible worlds} interpretation for modal logic:
\begin{itemize}
\item |FF| satisfies no process;
\item |TT| satisfies any process, including |Null|;
\item |(Conj fs)| satisfies |p| when $|p| \models |f|$ for all |f `elem` fs|;
\item |(Disj fs)| satisfies |p| when there exists |f `elem` fs| that $|p| \models |f|$;
\item |(Dia a f)| satisfies |p| when there exists a step from |p| labeled with |a| into |p'|
in the current world such that $|p'| \models |f|$;
\item |(Box a f)| satisfies |p| when any possible step from |p| to |p'| labeled with |a|
satisfies $|p'| \models |f|$ in all possible worlds;
\item (|Dia a (x.\f)|) and (|Box a (x.\f)|) are similar to above two items while
taking bound steps from |p| to |(x.\p')|;\footnote{There are some subtleties on
	what values (|v|) are to be chosen to instantiate |x| for both |(x.\p')|
	and |(x.\f)| in order to check $|subst x v {-"\!"-}p'| \models |subst x v {-"\!"-}f|$.
	The basic idea is that, for input action, all possible values should be considered
        whereas, for bound output action, |x| should be treated a fresh constant distinct from
	all the other names introduced before because |x| must have originated from
	the restricted process --- recall (open scope-ext) in Figure~\ref{fig:lts}.}
\item (|DiaMatch sigma f|) satisfies p when |x_i==y_i| holds for all |(x_i,y_i)`elem`sigma|
in the current world and $|p| \models |f|$; and
\item (|BoxMatch sigma f|) satisfies p when $|p| \models |f|$ in all possible worlds
such that |x_i==y_i| holds for all |(x_i,y_i)`elem`sigma|.
\end{itemize}

In the context of open bisimulation, possible worlds are 
determined by substitutions over the free names of processes.
For example, consider |TauP{-"\hspace{-.3ex}"-}(Match x y {-"\hspace{-.3ex}"-}tau)|.
In a world given by a substitution that unifies |x| and |y|
(i.e., both maps to same value), it can make two consecutive steps
labeled with |Tau|. On the other hand, in another world where the substitution
does not unify |x| and |y|, it can only make one |Tau|-step but no further.
Because open bisimulation is an equivalence property across all possible worlds,
|TauP{-"\hspace{-.3ex}"-}(Match x y {-"\hspace{-.3ex}"-}tau)| is bisimilar
to none of |tau|, |tautau|, and |Plus tau tautau|. In particular,
$|TauP{-"\hspace{-.3ex}"-}(Match x y {-"\hspace{-.3ex}"-}tau)| \not\sim_{\!o} |Plus tau tautau|$
exemplifies that open bisimulation distinguishes environment sensitive choices
made by match prefix from (environment insensitive) nondeterministic choices made by (|`Plus`|).

%% TODO do we say something about negation duality |Box| |Dia| thing here? or maybe better said in intro???
