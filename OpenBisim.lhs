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

\section{Open Bisimulation}
\label{sec:bisim}
In this section, we discuss the definition of simulation in Haskell
to provide an understanding for the definition of bisimulation, which
shares a similar structure but twice in length.
Figure~\ref{fig:sim} illustrates two versions of the simulation definition.
The first version
|sim :: Ctx{-"\!"-}->{-"\!"-}Pr{-"\!"-}->{-"\!"-}Pr{-"\!"-}->{-"\!"-}Bool|
is the usual simulation checker that returns a boolean value,
defined as a conjunction of the results from |sim_|.
The second version |sim'| is almost identical to |sim_| except
that it returns a forest that contains information about each simulation step.
Similarly, we have two versions for bisimulation,
|bisim| defined in terms of |bisim_| and |bisim'| that returns a forest.

A process |p| is (openly) simulated by another process |q|, that is
(|sim nctx p q|) where |nctx=[All{-"\!"-}x || x<-fv{-"\!"-}(p,q)]|,
when for every step from |p| to |p'| there exists a step from |q| to |q'|
labeled with the same action in the same word such that (|sim nctx p' q'|);%
\footnote{The function (|and :: [Bool] -> Bool|) implements "for every step"
	and the function (|or :: [Bool] -> Bool|) implements "there exists a step".}
also, similarly for every bound step lead by |p| to |(x.\p')| is
followed by |q| to |(x.\q')| such that (|sim nctx' p' q'|) where
|nctx'| is a context extended from |nctx| with |x|.
In the definition of |sim_| consists of |do|-blocks combined by
the alternative operator (\!|<||>|\!). The first |do|-block is for
the free step and the second is for the bound step. In the bound step case,
we make sure that the context (|nctx'|) used in the recursive calls after
following bound steps from |q| is extended by the same fresh variable (|x'|).%
\footnote{Having bound step children share the same fresh variable makes it more
convenient to generate the distinguishing formulae in Section~\ref{sec:df}.}

For bisimulation (|bisim nctx p q|), we consider both cases of either side
leading a step. Hence, the definition of |bisim| consists of four |do|-blocks
where the first two have the same structure as |sim_| lead by |p|,
and the other two are the cases lead by |q|. Note that
bisimulation (|bisim nctx p q|) is not the same as mutual simulation
(|sim nctx p q && sim nctx q p|) in general. In bisimulation, the leading and 
following sides do not always alternate regularly. For instance, after
the leading step from |p| to |p'| followed by |q| to |q'|, both cases of |p'|s
lead and |q'|s lead are considered in bisimulation whereas only |p'| continues
to lead in simulation. Hence, bisimulation distinguishes more processes than
mutual simulation.

Both versions of transition steps are used here:
the symbolic version (Figure~\ref{fig:OpenLTS}) for the leading step and
the fixed-world version (Figure~\ref{fig:IdSubLTS}) for the following step.
It is possible to implement bisimulation only using the symbolic version
because the fixed-world version can be understood as a symbolic transition
restricted to the identity substitution. More precisely, the properties
in Figure~\ref{fig:prop} hold. The fixed-world version is more efficient
because it avoids generating possible worlds other than the current one.
In contrast, the equivalent implementation using the symbolic transition
generates substitutions of other possible worlds only to be discard by
failing to match the empty list pattern.
\begin{figure}\small
\begin{spec}
      (runFreshMT $ IdSubLTS.one p :: [(Act,Pr)])
  ==  (runFreshMT $ do { ([],r) <- OpenLTS.one nctx p; return r } )
\end{spec}
\begin{spec}
      (runFreshMT $ IdSubLTS.oneb p :: [(ActB,PrB)])
  ==  (runFreshMT $ do { ([],r) <- OpenLTS.oneb nctx p; return r } )
\end{spec}%
\vspace*{-4.5ex}%
\caption{Equational properties between fixed-world and symobilic transition steps
	where |nctx| is a closing context of |p|.}
\label{fig:prop}
\vspace*{-1.5ex}
\end{figure}

The amount of change from |sim_| to |sim'| is small. The only differences are
that {\small|return.(and::[Bool]->Bool)|} and {\small|return.(or::[Bool]->Bool)|}
in each |do|-block of |sim_| are replaced by
{\small|returnL.One(...)|} and {\small|returnR.One(...)|} in the the free step case
and by
{\small|returnL.OneB(...)|} and {\small|returnR.OneB(...)|} in the bound step case
of |sim'|. The rest of the definition is exactly the same. Similarly, there are
twice amount of such differences between |bisim_| and |bisim'| to prepare for
the distinguishing formulae generation.

\begin{figure}\small
\begin{code}
module OpenBisim where
import PiCalc; import Control.Applicative; import Control.Monad
import OpenLTS; import qualified IdSubLTS; import Data.Tree
import Unbound.LocallyNameless hiding (empty)

data StepLog  =  One   Ctx EqC Act   Pr
              |  OneB  Ctx EqC ActB  PrB  deriving (Eq,Ord,Show)

returnL log = return . Node (Left log)   -- for the step on |p|'s side
returnR log = return . Node (Right log)  -- for the step on |q|'s side

sim nctx p q = and $ sim_ nctx p q

sim_ :: Ctx -> Pr -> Pr -> [Bool]
sim_ nctx p q  =    do  (sigma, r) <- runFreshMT (one nctx p); let sigmaSubs = subs nctx sigma
                        let (lp, p') = sigmaSubs r
                        return . (or :: [Bool] -> Bool) . runFreshMT $ do
                          (lq, q') <-IdSubLTS.one (sigmaSubs q)
                          guard $ lp == lq
                          return . (and :: [Bool] -> Bool) $ sim_ nctx p' q'
               <|>  do  (sigma, r) <- runFreshMT (oneb nctx p); let sigmaSubs = subs nctx sigma
                        let (lp, bp') = sigmaSubs r
                        let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bp'
                        return . (or :: [Bool] -> Bool) . runFreshMT $ do
                          (lq, bq') <-IdSubLTS.oneb (sigmaSubs q)
                          guard $ lp == lq
                          (x, q1, p1) <- unbind2' bq' bp'
                          let (p', q')  | x == x'    = (p1, q1)
                                        | otherwise  = subst x ((Var{-"\!"-}x')) (p1, q1)
                          let nctx' = case lp of   DnB _ -> All x' : nctx
                                                   UpB _ -> Nab x' : nctx
                          return . (and :: [Bool] -> Bool) $ sim_ nctx' p' q'

sim' :: Ctx -> Pr -> Pr -> [Tree (Either StepLog StepLog)]
sim' nctx p q   =     do   (sigma, r) <- runFreshMT (one nctx p); let sigmaSubs = subs nctx sigma
                           let (lp, p') = sigmaSubs r
                           returnL (One nctx sigma lp p') . runFreshMT $ do
                             (lq, q') <-IdSubLTS.one (sigmaSubs q)
                             guard $ lp == lq
                             returnR (One nctx sigma lq q') $ sim' nctx p' q'
                <|>   do   (sigma, r) <- runFreshMT (oneb nctx p); let sigmaSubs = subs nctx sigma
                           let (lp, bp') = sigmaSubs r
                           let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bp'
                           returnL (OneB nctx sigma lp bp') . runFreshMT $ do
                             (lq, bq') <-IdSubLTS.oneb (sigmaSubs q)
                             guard $ lp == lq
                             (x, p1, q1) <- unbind2' bp' bq'
                             let (p', q')   | x == x'    = (p1, q1)
                                            | otherwise  = subst x ((Var{-"\!"-}x')) (p1, q1)
                             let nctx' = case lp of   DnB _ -> All x' : nctx
                                                      UpB _ -> Nab x' : nctx
                             returnR (OneB nctx sigma lq bq') $ sim' nctx' p' q'

freshFrom :: Fresh m => [Nm] -> PrB -> m Nm
freshFrom xs b = do { mapM_ fresh xs; (y,_) <- unbind b; return y }
\end{code}
\vspace*{-3.5ex}
\caption{An implementation of the open simulation (|sim|) and its variant (|sim'|)
producing a forest.}
\label{fig:sim}
\end{figure}

%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
bisim nctx p q = and $ bisim_ nctx p q
bisim_ nctx p q =
  do (sigma, r) <- runFreshMT (one nctx p)
     let (lp, p') = subs nctx sigma r
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, q') <-IdSubLTS.one (subs nctx sigma q) -- follow with same sub and label
       guard $ lp == lq
       return . (and :: [Bool] -> Bool) $ bisim_ nctx p' q'
  <|>
  do (sigma, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = subs nctx sigma r
     let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bp' -- to use same new quan var
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, bq') <-IdSubLTS.oneb (subs nctx sigma q) -- follow with same sub and label
       guard $ lp == lq
       (x, p1, q1) <- unbind2' bp' bq'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       return . (and :: [Bool] -> Bool) $ bisim_ nctx' p' q'
  <|>
  do (sigma, r) <- runFreshMT (one nctx q)
     let (lq, q') = subs nctx sigma r
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lp, p') <-IdSubLTS.one (subs nctx sigma p) -- follow with same sub and label
       guard $ lp == lq
       return . (and :: [Bool] -> Bool) $ bisim_ nctx p' q'
  <|>
  do (sigma, r) <- runFreshMT (oneb nctx q)
     let (lq, bq') = subs nctx sigma r
     let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bq' -- to use same new quan var
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lp, bp') <-IdSubLTS.oneb (subs nctx sigma p) -- follow with same sub and label
       guard $ lp == lq
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       return . (and :: [Bool] -> Bool) $ bisim_ nctx' p' q'


bisim' nctx p q =
  do (sigma, r) <- runFreshMT (one nctx p)
     let (lp, p') = subs nctx sigma r
     returnL (One nctx sigma lp p') . runFreshMT $ do
       (lq, q') <-IdSubLTS.one (subs nctx sigma q) -- follow with same sub and label
       guard $ lp == lq
       returnR (One nctx sigma lq q') $ bisim' nctx p' q'
  <|>
  do (sigma, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = subs nctx sigma r
     let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bp' -- to use same new quan var
     returnL (OneB nctx sigma lp bp') . runFreshMT $ do
       (lq, bq') <-IdSubLTS.oneb (subs nctx sigma q) -- follow with same sub and label
       guard $ lp == lq
       (x, p1, q1) <- unbind2' bp' bq'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       returnR (OneB nctx sigma lq bq') $ bisim' nctx' p' q'
  <|>
  do (sigma, r) <- runFreshMT (one nctx q)
     let (lq, q') = subs nctx sigma r
     returnR (One nctx sigma lq q') . runFreshMT $ do
       (lp, p') <-IdSubLTS.one (subs nctx sigma p) -- follow with same sub and label
       guard $ lp == lq
       returnL (One nctx sigma lp p') $ bisim' nctx p' q'
  <|>
  do (sigma, r) <- runFreshMT (oneb nctx q)
     let (lq, bq') = subs nctx sigma r
     let x' = runFreshM $ freshFrom (quan2nm<$>nctx) bq' -- to use same new quan var
     returnR (OneB nctx sigma lq bq') . runFreshMT $ do
       (lp, bp') <-IdSubLTS.oneb (subs nctx sigma p) -- follow with same sub and label
       guard $ lp == lq
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       returnL (OneB nctx sigma lp bp') $ bisim' nctx' p' q'
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%

\begin{figure}\small
\savecolumns
\begin{code}
forest2df :: [Tree (Either StepLog StepLog)] -> [(Form,Form)] {-"\hspace{10ex}"-}
forest2df rs
            =    do  Node (Left (One _ sigma_p a _)) [] <- rs
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (prebase sigma_p a {-"\,"-},{-"\;"-} postbase sigmaqs a)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                 do  Node (Right (One _ sigma_q a _)) [] <- rs
                     let formR = prebase sigma_q a
                     let sigmaps = subsMatchingAct a (left1s rs)
                     return (postbase sigmaps a, formR)
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
            <|>  do  Node (Left (OneB _ sigma_p a _)) [] <- rs
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (preBbase sigma_p a {-"\,"-},{-"\;"-} postBbase sigmaqs a)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                 do  Node (Right (OneB _ sigma_q a _)) [] <- rs
                     let formR = preBbase sigma_q a
                     let sigmaps = subsMatchingActB a (left1Bs rs)
                     return (postBbase sigmaps a, formR)
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
            <|>  do  Node (Left (One _ sigma_p a _)) rsR <- rs
                     let rss' = [rs' | Node _ rs' <- rsR]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (pre sigma_p a dfsL {-"\,"-},{-"\;"-} post sigmaqs a dfsR)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                 do  Node (Right (One _ sigma_q a _)) rsL <- rs
                     let rss' = [rs' | Node _ rs' <- rsL]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaps = subsMatchingAct a (left1s rs)
                     return (post sigmaps a dfsL, pre sigma_q a dfsR)
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
\begin{code}
            <|>  do  Node (Left (OneB nctx sigma_p a _)) rsR <- rs
                     let  rss' = [rs' | Node _ rs' <- rsR]
                          x = quan2nm . head . getCtx . fromEither
                            . rootLabel . head $ head rss'
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (preB sigma_p a x dfsL {-"\,"-},{-"\;"-} postB sigmaqs a x dfsR)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
\end{code}
\vspace*{-4.7ex}
%if False %%%% BEGIN omit from LaTeX %%%%%%%%%%%%%%%%%%
\begin{code}
                 do  Node (Right (OneB nctx sigma_q a _)) rsL <- rs
                     let  rss' = [rs' | Node _ rs' <- rsL]
                          x = quan2nm . head . getCtx . fromEither . rootLabel
                                $ head (head rss')
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaps = subsMatchingActB a (left1Bs rs)
                     return (postB sigmaps a x dfsL, preB sigma_q a x dfsR)
\end{code}
%endif    %%%% END   omit from LaTEX %%%%%%%%%%%%%%%%%%
\restorecolumns
\savecolumns
%{
%format sigmas = "\sigma{}\hspace{-.3ex}s"
\begin{code}
  where
    prebase sigma a = pre sigma a []
    postbase sigmas a = post sigmas a []
    preBbase sigma a = preB sigma a (s2n "?") []
    postBbase sigmas a = postB sigmas a (s2n "?") []
    pre sigma a = boxMat sigma . Dia a . conj
    post sigmas a fs = Box a . disj $ {-"\,"-} (diaMat<$>sigmas) ++ fs
    preB sigma a x = boxMat sigma . DiaB a . bind x . conj
    postB sigmas a x fs = BoxB a . bind x . disj $ {-"\,"-} (diaMat<$>sigmas) ++ fs
    boxMat  [] = id; boxMat  sigma = BoxMatch [(Var x,Var y) | (x,y)<-sigma]
    diaMat  [] = FF; diaMat  sigma = DiaMatch [(Var x,Var y) | (x,y)<-sigma] TT
    right1s  rs = [log | Node (Right  log@(One{})) _ <- rs]
    left1s   rs = [log | Node (Left   log@(One{})) _ <- rs]
    right1Bs  rs = [log | Node (Right  log@(OneB{})) _ <- rs]
    left1Bs   rs = [log | Node (Left   log@(OneB{})) _ <- rs]
    getCtx (One   nctx _ _ _)  = nctx; getCtx (OneB  nctx _ _ _) = nctx
    fromEither (Left   t) = t; fromEither (Right  t) = t

subsMatchingAct :: Act -> [StepLog] -> [EqC]
subsMatchingAct a logs =
  do  One nctx sigma a' _ <-logs           {-"\;"-};{-"~"-}  let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a'  {-"\;"-};{-"~"-}  return sigma

subsMatchingActB :: ActB -> [StepLog] -> [EqC]
subsMatchingActB a logs =
  do  OneB nctx sigma a' _ <-logs          {-"\;"-};{-"~"-}  let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a'  {-"\;"-};{-"~"-}  return sigma
\end{code}
%}
\vspace*{-3.5ex}
\caption{Generating distinguishing formulae from the forest produced by |bisim'|.}
\label{fig:df}
\end{figure}

\section{Distinguishing Formulae Generation}
\label{sec:df}
The distinguishing formulae generation is no more than a tree transformation.
(Figure~\ref{fig:df}), which generates a pair of
distinguishing formulae from the forest of rose trees produced
by |(bisim' nctx p q)|. The first formula is satisfied by the left process (|p|)
but fails to be satisfied by the other. Likewise, the second formula is
satisfied by the right process (|q|) but not by the other. The tree transformation
function |forest2df| returns a list (|[(Form,Form)]|) because there can be more
than one pair of such formulae for the given non-bisimilar processes.
For bisimilar processes, |forest2df| returns the empty list. The definition of
|forest2df| consists of eight |do|-blocks where the first four are base cases
and the latter four are inductive cases. We only illustrate the cases lead by
the left side (|p|) while the cases lead by the right side (|q|) are omitted
in Figure~\ref{fig:df}.

It is a base case when the leading step has no matching following step.
That is, the children following the leading step specified by the root label of
the tree is an empty list, as you can observe from the beginning lines of
the first and third |do|-blocks in Figure~\ref{fig:df}. 
%% The forest |rs| is a list of trees whose root labels contain information about
%% the leading steps and their children have the information on the following steps.
%% That is, a base case is when the children of a tree in |rs| is an empty list,
The formula satisfied by the leading side is
|(DiaMatch sigma_p (Dia a TT))| or |(DiaMatch sigma_p (DiaB a (w.\TT))|,
generated by |prebase| or |preBbase|, whose intuitive meaning is that
the process can make a step labeled with |a| in the world given by |sigma_p|.
This formula clearly fails to be satisfied by the other side because there is
no following step (i.e., step labeled with |a| from |q| in the |sigma_p|-world)
for the base case. If there were only one world to consider, the formula for
the other side would be |(Box a FF)| or |(BoxB a (w.\FF))|, meaning that
the process cannot make a step labeled with |a|. However, we must consider
the possible worlds where such step exists for the following side.
Such worlds (|sigmaqs|) are collected from the sibling nodes of the leading step
using the helper functions |subsMatchingAct| and |subsMatchingActB|.
The formula satisfied by the following side is
|(Box (DiaMatch sigmaqs TT))| or |(BoxB (w.\DiaMatch sigmaqs TT)|,
generated by |postbase| or |postBbase|.

In an inductive case where the leading step from |p| to |p'| is matched
by a following step |q| to |q'|, we find a pair of distinguishing formulae
for each pair of |p'| and |q'| at next step by recursively applying |forst2df|
to all the grandchildren following the steps lead by |p|, that is,
|(sequence (forest2df <||> rss')) :: [(Form,Form)]|.
The this list should not be empty; otherwise it had either been a base case
or it had been a forest generated from bisimilar processes.
The collected the left biased formulae (|dfsL|) are used for constructing
the distinguishing formula satisfied by the leading side in the fifth and
seventh |do|-blocks in Figure~\ref{fig:df}, which is
|(BoxMatch sigma_p (Dia a (Conj dfsL)))| or
|(BoxMatch sigma_p (DiaB a (w.\Conj dfsL)))| where |w| is fresh in |dfsL|.
Similarly, the right biased formulae (|dfsR|) are used for constructing
the formula satisfied by the other side, which is
|(Box a (Disj (DiaMatch sigmaqs TT ++ dfsR)))| or
|(BoxB a (x.\Disj (DiaMatch sigmaqs TT ++ dfsR)))|.
Here, |x| corresponds to the |x'| in Figure~\ref{fig:sim}, which is
the fresh variable extending the context. Because we made sure that
the same variable is used to extend the context across
all the following bound steps from a leading step, we simply need to select
the first one, using some number of selector functions to go inside the list,
retrieve the context from the root, and grab the name
in the first quantifier of the context.


%%%%%% Discussion section included from here %%%%%%%%%%%%%%%%%%%%%%%%
%include discuss.lhs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
