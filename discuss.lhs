%%% included from OpenBisim.lhs
\section{Discussions}
\label{sec:discuss}
We point out three advantages of using Haskell for our problem of
generating distinguishing formulae (Section~\ref{sec:discuss:adv})
and discuss further optmizations and extensions to our current
implementation presented in this paper (Section~\ref{sec:discuss:fur}).%
\vspace*{-1.5ex}
\subsection{Advantages of using Haskell}
\label{sec:discuss:adv}
First, having a well-tailored generic name binding library such as
\textsf{unbound}~\cite{unbound11} saves a great amount of effort
on tedious boilerplate code for keeping track of freshness, 
collecting free variables, and capture-avoiding substitutions.
Due to value passing and name restriction in the $\pi$-calculus,
frequent management of name bindings is inevitable in implementations
involving the $\pi$-calculus.

Second, lazy evaluation and monadic encoding of nondeterminism in Haskell
makes it natural to view \emph{control flow} as \emph{data}.
Distinguishing formula generation can be defined as a tree transformation
(|forest2df|) over the forest of rose trees lazily produced from |bisim'|.
Only a small amount of change was needed to abstract the control flow of
computing a boolean by |bisim| into data production by |bisim'|.

The forest produced by |bisim'| is all possible traces of bisimulation steps.
The control flow of |bisim| for non-bisimilar processes
corresponds to a depth-first search traversal
% (by the semantics of list monad)
until the return value is determined to be |False|.
% (by short circuiting of the boolean operation |and|).
For bisimilar processes, |bisim| returns |True| after the exhaustive traversal.

The traversal during the formulae generation
does not exactly match the pattern of traversal by |bisim|.
Alongside the depth-first search, there are traversals across the siblings of
the leading step to collect |sigmaqs| in Figure~\ref{fig:df}.
% using the helper functions |subsMatchingAct| and |subsMatchingActB|.

For process calculi with less sophisticated semantics, it is possible to log
a run of bisimulation check and construct distinguishing formulae using
the information from those visited nodes only. In contrast, we need additional
information on other possible worlds, which come from the nodes not necessarily
visited by |bisim|.

Third, constraints are first-class values in constraint programming using Haskell.
We construct distinguishing formulae using substitutions (i.e., equality constraints)
as values (e.g., |sigma_p| and |sigmaqs| in Figure~\ref{fig:df}).
This is not quite well supported in (constraint) logic programming.
For example, consider a Prolog code fragment,
$\mathtt{ \cdots {\scriptsize\textcircled{1}}\,
            X=Y, {\scriptsize\textcircled{2}}\,
            Z=W, {\scriptsize\textcircled{3}}\, \cdots }$,
and let $\sigma_1$, $\sigma_2$, and $\sigma_3$ be the equality constraints at
the points marked by {\scriptsize\textcircled{1}}, {\scriptsize\textcircled{2}},
and {\scriptsize\textcircled{3}}. We understand that it should be
$\mathtt{\sigma_1\cup\{X=Y\}\equiv\sigma_2}$ and
$\mathtt{\sigma_2\cup\{Z=W\}\equiv\sigma_3}$.
However, $\sigma_1$, $\sigma_2$, and $\sigma_3$ are not values in a logic programming language.
% In fact, accessing the constraint store in logic programming systems
% goes against the logic programming paradigm.

The labeled transition semantics and open bisimulation can be elegantly
specified in higher-order logic programming systems~\cite{TiuMil10};
for those purposes, it fits better than functional programming. However, generating
certificates regarding open bisimulation requires the ability that amounts to
accessing meta-level properties of logic programs (e.g., substitutions) across
nondeterminisitc execution paths, where it is preferable to have constraints
as fist-class values.%
\vspace*{-1.5ex}
\subsection{Further Optimizations and Extensions}
\label{sec:discuss:fur}
One obvious optimization to our current implementation is to represent
the equality constraints as partitions instead of computing partitions
from the list of name pairs on the fly every time we need a substitution function.

We can enrich the term structure to model applied variants of $\pi$-calculi
by supporting unification in a more general setting \cite{Miler92uum} and
constraints other than the equalities solvable by unification. When the constraints
become more complex, we can no longer model them as integer set partitions. In addition,
it would be better to abstract constraint handling with another layer of monad
(e.g., state monad).  In this work, we did not bother to abstract the constraints
in a monad because they were very simple equalities over names only.

To handle infinite processes (or finite but quite large ones) effectively,
we should consider using more sophisticated search strategies. For this,
we would need to replace the list monad with a custom monad equipped with
better control over traversing the paths of nondeterministic computation.
Thanks to the monadic abstraction, the definitions could remain mostly the same
and only their type signatures would be modified to use the custom monad.

Memoization or tabling is a well known optimization technique to avoid
repetitive computation by storing results of computations associated with
their input arguments. When we have infinite processes, this is no longer
an optional optimization but a means to implement the coinductive definition of
bisimulation over possibly infinite transition paths.
Parallel computing may also help to improve scalability of traversing over
large space of possible transitions but memoization could raise additional
concurrency issues \cite{ZiaSivJag09,Bergstrom13phd}.
