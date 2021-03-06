%include mylhs2tex.lhs
\section{Introduction}
\label{sec:intro}
The main idea of this paper is that Haskell and its libraries provide
a great platform for analyzing behaviors of nondeterministic transition systems 
in a symbolic way. Our main contribution is identifying an interesting problem
from process calculus and demonstrating its solution in Haskell that supports
this idea. More specifically, we implement automatic generation of
modal logic formulae for two non-open bisimilar processes in the $\pi$-calculus,
which can be machine-checked to witness that the two processes are indeed distinct.

In this section, we give a brief background on the $\pi$-calculus, bisimulation,
and its characterizing logic; discuss the motivating example; and summarize
our contributions. %\vspace*{-2ex}

\paragraph{The $\pi$-calculus}\hspace{-1.5ex}\cite{Milner92picalcI,Milner92picalcII}
is a formal model of concurrency meant to capture a notion of mobile processes.
The notion of {\em names} plays a central role in this formal model;
communication channels are presented by names; mobility is represented by
scoping of names and {\em scope extrusion} of names. The latter is captured in
the operational semantics via transitions that may send a restricted channel name,
and thereby enlarging its scope.
There are several bisimulation equivalences for the $\pi$-calculus,
%%The name-passing features of the $\pi$-calculus induces several variants of
%% bisimulation equivalences,
notably, early \cite{Milner92picalcII}, 
late~\cite{Milner92picalcII}, and open~\cite{Sangiorgi96acta} bisimilarities.
Only the latter is a congruence and is of main interest in this paper.

Bisimulation equivalence can be alternatively characterized using modal logics.
A modal logic is said to characterize a bisimilarity relation if whenever
two processes are bisimilar then they satisfy the same set of assertions in that modal logic
and vice versa. Such a characterization is useful for analyzing
why bisimulation between two processes fails, since an explicit witness of
non-bisimilarity, in the form of a modal logic formula (also called
a {\em distinguishing formula}), can be constructed such that
one process satisfies the formula while the other does not.
Early and late bisimilarities can be characterized using fragments of
Milner-Parrow-Walker (MPW) logic~\cite{MilParWal93lm}, and a characterization of
open bisimilarity has been recently proposed by \citet{AhnHorTiu17corr} using
a modal logic called \OM. Our work can be seen as a companion of the latter,
showing that the construction of the distinguishing formula described there can
be effectively and naturally implemented in Haskell. 

% What makes open bisimulation attractive is that it is effectively
% implementable (see, e.g.,\cite{VicMol94mwb,TiuMil10}),
% and has been shown useful to reason about processe equivalence, applied in
% the setting of protocol analysis~\cite{TiuNamHor16spec}.
One main complication in implementing bisimulation checking for the $\pi$-calculus
(and name passing calculi in general) is that the transition system that
a process generates can have infinitely many states, so the traditional
partition-refinement-based algorithm for computing bisimulation and
distinguishing formulae~\cite{Cleaveland90} does not work. Instead,
one needs to construct the state space `on-the-fly', similar to that done in
the Mobility Workbench~\cite{VicMol94mwb}. In our work, this on-the-fly
construction is basically encapsulated in Haskell's lazy evaluation of
the search trees for distinguishing formulae. Another complicating factor is
that in $\pi$-calculus, fresh names can be generated and extruded,
and one needs to keep track of the relative scoping of names.
This is particularly
relevant in open bisimulation, where input names are treated symbolically
(i.e., represented as variables), so care needs to be taken so that,
for example, a variable representing an input name cannot be instantiated by
a fresh name generated after the input action. For this, we rely on
the \textsf{unbound} library~\cite{unbound11}, which uses a locally nameless
representation of terms with binding structures, to represent processes with
bound names and fresh name generation.

% The symbolic nature of input names in open bisimulation is in fact a source of much complication
% in defining a modal logic that characterizes it. In particular, the modal logic $\mathcal{OM}$
% is intuitionistic, unlike MPW logic which is classical. A consequence of this is, as shown in \cite{},
% in constructing a distinguishing formula for non-bisimilar processes $P \not \sim Q$,
% one needs to construct two formula at the same time, one with a `bias' to $P$ (i.e., satisfied by $P$ but not $Q$)
% and the other with a bias to $Q$, and the two formula may not be dual to each other in general.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%55


%include exampleFigure.lhs

\paragraph{A motivating example\!\!}\!\! in Figure~\ref{fig:example} illustrates
two processes (left-hand side of $\models$), their distinguishing formulae
(right-hand side of $\models$), and all essential steps in an attempt to construct
a bisimulation. We give here only a high-level description of a bisimulation checking
process as search trees and postpone the detail explanation of the syntax and the operational
semantics of $\pi$-calculus to Section~\ref{sec:syntax}.

% Each process is a nondeterministic sum (or choice) of two subprocesses,
% hence, each has two possible transitions.
Bisimulation can be seen as a two-player game, where
every step of a player must be matched by a step by the opponent. In the figure,
the steps by the player (which we refer to as the leading steps) are
denoted by line arrows, whereas the steps by the opponent (the following steps)
are denoted by dotted arrows. 
%leading steps.
There are initially four leading steps to consider, corresponding to the cases where
$P$ moves first ((1) and (2)) and where $Q$ moves first ((3) and (4)).
% Each transition arrow is labelled with an action ($\tau$
% in this case) and a name substitution (represented as a list of pairs of names).
% Note that in open bisimulation, one needs to consider all possible name substitutions
% in every leading step, so in principle the bisimulation set is infinite if it exists.
% However, such an infinite set can usually be finitely represented~\cite{}.

%% because any side may lead
%% in bisimulation.
% Two processes are bisimilar when for every leading step there exists
% a following step such that the evolved processes after the step are bisimilar.

Let us visually examine whether each leading step meets the condition for bisimilarity:
(1) clearly fails the condition because no dotted arrow follows the last line arrow;
(2) clearly satisfies the condition with exactly only one dotted arrow and no more;
(3) satisfies it by taking the left branch where the subtree satisfies the condition;
and (4) also satisfies it by taking the right branch. Therefore, they are
not open bisimilar ($P \not\sim_{\!o} Q$) due to the failure in (1).

%% A bisimulation checking algorithm by
A depth first search for bisimulation, scanning from left to
right, only needs to traverse the first tree (1) to notice non-bisimilarity.
Our existing bisimulation checker (prior to this work) is
a higher-order logic program, which runs in this manner.
However, the witness we want to generate contains extra information
(\uwave{wavy underlined}), which are not found in (1) but in (3). Therefore,
simply logging all the visited steps during a run of a bisimulation check
is insufficient.

The extra information {\small|sigma=[(x,y)]|} represents a substitution
that unifies |x| and |y|. The third tree (3) considers the leading step
initiated by the subprocess |Match x y (TauP (TauP Null))|, which
%% is only possible to
can only make a step in a world (or environment)
where |x| and |y| are equivalent. Our earlier implementation uses
a logic programming language,
%% takes advantage of logic programming by representing
relying on a representation of |x| and |y| as unifiable logic variables and 
%% by relying
on backtracking for nondeterminism.
However, it is difficult to access |sigma| in this setting because |sigma|
resides inside the system state rather than being a first-class value.
Access to logic variable substitutions since the definition of
open bisimulation and the generation of distinguishing formulae
require access to and manipulations of such substitutions.
Moreover,
the information is lost when backtracking to another branch, for instance,
from (3) to (4).

On the other hand, it is very natural in Haskell to view all possible
nondeterministic steps as tree structured data because of laziness.
Once we are able to produce the trees in Figure~\ref{fig:example}
(Section~\ref{sec:bisim}), our problem reduces to a transformation
from trees to formulae (Section~\ref{sec:df}). Thanks to laziness,
only those nodes demanded by the tree transformation function will
actually be computed. We also have constraints (i.e., substitutions)
as first-class values with an overhead of being more explicit about
substitutions compared to logic programming.

In order to produce the trees of bisimulation steps, we first
need to define the syntax (Section~\ref{sec:syntax:pi}) and
semantics (Section~\ref{sec:lts}) of the $\pi$-calculus in Haskell.
We also need to define the syntax of our modal logic formulae
(Section~\ref{sec:syntax:om}) for the return value of
the tree transformation function. However, we do not need to
implement the semantics of the logic because we can check the generated formulae
with our existing formula satisfaction ($\models$) checker.

\paragraph{Our contributions}\hspace{-1.5ex} are summarized as follows:\vspace*{-.75ex}
\begin{itemize}
\item
We identified a problem that generating certificates witnessing the failure of
process equivalence checking is non-trivial in a logic programming setting
(Figure~\ref{fig:example}), even though the equivalence property itself has been
elegantly specified as a logic program.
\vspace*{.5ex}
\item
The crux of our solution is a tree transformation from the forest of all possible
bisimulation steps to a pair of distinguishing formulae (Section~\ref{sec:df}).
The definition of tree transformation (Figure~\ref{fig:df}) is clear and easy to
understand because we are conceptually working on all possible nondeterministic steps.
Nevertheless, unnecessary computations are avoided by laziness.
\vspace*{.5ex}
\item
We demonstrate that the overhead of re-implementing the syntax
(Section~\ref{sec:syntax}), labeled transition semantics (Section~\ref{sec:lts}),
and open bisimulation checker (Section~\ref{sec:bisim}) in Haskell, which
we already had as a logic program, and then augmenting it to produce trees
is relatively small. In fact, most of the source code, omitting repetitive
symmetric cases, is laid out as figures (Figures~\ref{fig:PiCalc},\,\ref{fig:IdSubLTS},\,\ref{fig:OpenLTS},\,\ref{fig:figureOpenLTS},\;and\;\ref{fig:sim}).%
\vspace*{.5ex}
\item
Our implementation of generating distinguishing formulae is a pragmatic evidence
that reassures our recent theoretical development~\cite{AhnHorTiu17corr} of
the modal logic \OM\ being a characterizing logic for open bisimilarity
(i.e., distinguishing formulae exists iff non-open bisimilar). In this paper,
we define the syntax of \OM\ formulae in Haskell and explain their intuitive
meanings (Section~\ref{sec:syntax:om}), and provide pointers to related work
(Section~\ref{sec:relwork}).
\end{itemize}
We used \textsf{lhs2TeX} to formatt the paper from literate haskell scripts
({\small\url{https://github.com/kyagrd/hs-picalc-unbound-example}}).

