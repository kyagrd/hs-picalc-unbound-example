{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
module OpenBisim where
import           Control.Applicative
import           Data.Foldable (asum)
import           Control.Monad
import qualified Data.List                       as List
import qualified Data.Set                        as Set
import           Data.Tree
import           Debug.Trace
import qualified IdSubLTS
import           MemoUgly
import           OpenLTS                         hiding (one, oneb)
import           PiCalc
import           Unbound.LocallyNameless         hiding (empty)
{-# ANN module "HLint: ignore Use mappend" #-}

data StepLog  =  One   Ctx NmSet EqC (EqC,EqC) Act   Pr
              |  OneB  Ctx NmSet EqC (EqC,EqC) ActB  PrB  deriving (Eq,Ord,Show)

returnL log = return . Node (Left log)   -- for the step on |p|'s side
returnR log = return . Node (Right log)  -- for the step on |q|'s side


freshFrom :: Fresh m => [Nm] -> PrB -> m Nm
freshFrom xs b = do { mapM_ fresh xs; fst <$> unbind b }

deltaExplode delta (ctx@(nctx,_,_), sigma, ns) =
  do (nctx', sigma', ns') <- deltaExplode_ delta (nctx, part2eqc ctx sigma, ns)
     guard $ respects sigma' nctx' ns'
     return (toCtx' nctx', fst $ mkPartitionFromEqC nctx' sigma', ns')

deltaExplode_ []            (nctx, cs, ns)    = pure (nctx, cs, ns)
deltaExplode_ ((x,y):delta) (nctx, cs, ns)
  | x == y    = error $ show (x,y) ++ " in delta"
  | Set.member x ns || Set.member y ns  = deltaExplode_ delta (nctx, cs, ns)
  | otherwise =
        deltaExplode_ delta (diffCtx (x,y) nctx, cs, Set.insert x ns)
    <|> asum [deltaExplode_ delta (nctx, (x,n):cs, ns) | n <- Set.toList ns]
    <|> deltaExplode_ delta (diffCtx (y,x) nctx, cs, Set.insert y ns)
    <|> asum [deltaExplode_ delta (nctx, (y,n):cs, ns) | n <- Set.toList ns]
  where
    diffCtx (x,y) nctx = {- trace (show $ nctx1 ++ Nab x : nctx2 ) $ -}
                         nctx1 ++ x : nctx2
       -- where (nctx1, nctx2) = span ((y/=).quan2nm) $ filter ((x/=) . quan2nm) nctx
       where (nctx1, _ : nctx2) = span (x/=) nctx -- span ((y/=).quan2nm) $ filter ((x/=) . quan2nm) nctx

unVar (Var x) = x

sim2 ctx ns p q = and $ sim2_ ctx ns p q

sim2_ :: Ctx' -> NmSet -> Pr -> Pr -> [Bool]
sim2_ ctx@(nctx,_,_) ns p q  =
       do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns p)
           (ctx, sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lp, p') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, q') <- IdSubLTS.one (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ sim2_ ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx',ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma'
           let (lp, p') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             q' <- IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns') (sigmaSubs q) lp
             return . (and :: [Bool] -> Bool) $ sim2_ ctx' ns p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lp, bp') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bp'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, bq') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ sim2_ ctx' ns' p' q'


bisim2 ctx ns p q = and $ bisim2_ ctx ns p q

bisim2_ :: Ctx' -> NmSet -> Pr -> Pr -> [Bool]
bisim2_ ctx@(nctx,_,_) ns p q  =
       do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns p)
           (ctx, sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lp, p') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, q') <- IdSubLTS.one (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx',ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma'
           let (lp, p') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             q' <- IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q) lp
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx' ns' p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lp, bp') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bp'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, bq') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx' ns' p' q'
  <|>  do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns q)
           (ctx, sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lq, q') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lp, p') <- IdSubLTS.one (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs p)
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns q)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx',ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma'
           let (lq, q') = sigmaSubs r
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             p' <- IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns') (sigmaSubs p) lq
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx' ns' p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns q)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma'
           let (lq, bq') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bq'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lp, bp') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs p)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ bisim2_ ctx' ns' p' q'


sim2' :: Ctx' -> NmSet -> Pr -> Pr -> [Tree (Either StepLog StepLog)]
sim2' ctx@(nctx,_,_) ns p q  =
       do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, p') = sigmaSubs r
           returnL (One nctx ns sigma_d (sigma_,delta) lp p') . runFreshMT $ do
             (lq, q') <- IdSubLTS.one ns (sigmaSubs q)
             guard $ lp == lq
             returnR (One nctx ns sigma_d (sigma_,delta) lq q') $ sim2' ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx'@(nctx',_,_),ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, p') = sigmaSubs r
           returnL (One nctx' ns' sigma_d (sigma_,delta) lp p') . runFreshMT $ do
             q' <-IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns') (sigmaSubs q) lp
             returnR (One nctx' ns' sigma_d (sigma_,delta) lp q') $ sim2' ctx' ns p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, bp') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bp'
           returnL (OneB nctx ns sigma_d (sigma_,delta) lp bp') . runFreshMT $ do
             (lq, bq') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             returnR (OneB nctx ns sigma_d (sigma_,delta) lq bq') $ sim2' ctx' ns' p' q'


bisim2' :: Ctx' -> NmSet -> Pr -> Pr -> [Tree (Either StepLog StepLog)]
bisim2' ctx@(nctx,_,_) ns p q  =
       do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma;  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, p') = sigmaSubs r
           returnL (One nctx ns sigma_d (sigma_,delta) lp p') . runFreshMT $ do
             (lq, q') <- IdSubLTS.one (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             returnR (One nctx ns sigma_d (sigma_,delta) lq q') $ bisim2' ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx'@(nctx',_,_),ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma;  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, p') = sigmaSubs r
           returnL (One nctx' ns' sigma_d (sigma_,delta) lp p') . runFreshMT $ do
             q' <- IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns') (sigmaSubs q) lp
             returnR (One nctx' ns' sigma_d (sigma_,delta) lp q') $ bisim2' ctx' ns p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns p)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lp, bp') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bp'
           returnL (OneB nctx ns sigma_d (sigma_,delta) lp bp') . runFreshMT $ do
             (lq, bq') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs q)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             returnR (OneB nctx ns sigma_d (sigma_,delta) lq bq') $ bisim2' ctx' ns' p' q'
  <|>  do  ((sigma,delta), r@(Tau,_)) <- runFreshMT (one_ ctx ns q)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lq, q') = sigmaSubs r
           returnR (One nctx ns sigma_d (sigma_,delta) lq q') . runFreshMT $ do
             (lp, p') <- IdSubLTS.one (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs p)
             guard $ lp == lq
             returnL (One nctx ns sigma_d (sigma_,delta) lp p') $ bisim2' ctx ns p' q'
  <|>  do  ((sigma,delta), r@(Dn _ (Var y),_)) <- runFreshMT (one_ ctx ns q)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let (ctx'@(nctx',_,_),ns')
                 | y `elem` (fv nctx :: [Nm]) || Set.member y ns  = (ctx,ns)
                 | otherwise  = (extend y ctx, Set.insert y ns)
           let sigmaSubs = subs_ ctx' sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lq, q') = sigmaSubs r
           returnR (One nctx' ns' sigma_d (sigma_,delta) lq q') . runFreshMT $ do
             p' <- IdSubLTS.oneIn (Set.map(unVar.sigmaSubs.Var)ns') (sigmaSubs p) lq
             returnL (One nctx' ns' sigma_d (sigma_,delta) lq p') $ bisim2' ctx' ns p' q'
  <|>  do  ((sigma,delta), r) <- runFreshMT (one_b ctx ns q)
           (ctx@(nctx,_,_), sigma', ns) <- deltaExplode delta (ctx, sigma, ns)
           let sigmaSubs = subs_ ctx sigma';  sigma_ = part2eqc ctx sigma
               sigma_d = part2eqc ctx sigma' List.\\ sigma_
           let (lq, bq') = sigmaSubs r
           let x' = runFreshM $ freshFrom (fv nctx) bq'
           returnR (OneB nctx ns sigma_d (sigma_,delta) lq bq') . runFreshMT $ do
             (lp, bp') <- IdSubLTS.oneb (Set.map(unVar.sigmaSubs.Var)ns) (sigmaSubs p)
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ctx' = extend x' ctx;  ns' = Set.insert x' ns
             returnL (OneB nctx ns sigma_d (sigma_,delta) lp bp') $ bisim2' ctx' ns' p' q'




-- wrapper -----------------------------
sim nctx = sim2 (toCtx' nctx)
sim' nctx = sim2' (toCtx' nctx)
bisim nctx = bisim2 (toCtx' nctx)
bisim' nctx = bisim2' (toCtx' nctx)
----------------------------------------

forest2df :: [Tree (Either StepLog StepLog)] -> [(Form,Form)]
forest2df rs
            =    do  rsL <- groupL1sBySdA rs
                     guard $ all (\(Node _ rs) -> null rs) rsL
                     Node (Left (One _ _ _ sd a _)) [] <- rsL
                     let formL = prebase sd a
                     let sd_qs = sdMatchingAct a (right1s rs)
                     return (formL, postbase sd_qs a)
            <|>  do  rsR <- groupR1sBySdA rs
                     guard $ all (\(Node _ rs) -> null rs) rsR
                     Node (Right (One _ _ _ sd a _)) [] <- rsR
                     let formR = prebase sd a
                     let sd_ps = sdMatchingAct a (left1s rs)
                     return (postbase sd_ps a, formR)
            <|>  do  rsL <- groupL1BsBySdA rs
                     guard $ all (\(Node _ rs) -> null rs) rsL
                     Node (Left (OneB _ _ _ sd a _)) [] <- rsL
                     let formL = preBbase sd a
                     let sd_qs = sdMatchingActB a (right1Bs rs)
                     return (formL, postBbase sd_qs a)
            <|>  do  rsR <- groupR1BsBySdA rs
                     guard $ all (\(Node _ rs) -> null rs) rsR
                     Node (Right (OneB _ _ _ sd a _)) [] <- rsR
                     let formR = preBbase sd a
                     let sd_ps = sdMatchingActB a (left1Bs rs)
                     return (postBbase sd_ps a, formR)
            <|>  do  rsL <- groupL1sBySdA rs
                     Node (Left (One _ ns sigma_d sd@(sigma,delta) a _)) rsR <- rsL
                     let rss' = [rs' | Node _ rs' <- rsR]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     -- guard . not . null $ dfsL
                     let sd_qs = sdMatchingAct a (right1s rs)
                         sd_qs' = do (s, d) <-sd_qs
                                     let s' = s List.\\ sigma
                                         d' = [(x,y) | (x,y) <- d, not(Set.member x ns || Set.member y ns)]
                                     guard $ not(null s' && null d')
                                     return (s', d')
                     return (pre sd a dfsL, post sd_qs' a dfsR)
            <|>  do  rsR <- groupR1sBySdA rs
                     Node (Right (One _ ns sigma_d sd@(sigma,delta) a _)) rsL <- rsR
                     let rss' = [rs' | Node _ rs' <- rsL]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     -- guard . not . null $ dfsR
                     let sd_ps = sdMatchingAct a (left1s rs)
                         sd_ps' = do (s, d) <-sd_ps
                                     let s' = s List.\\ sigma
                                         d' = [(x,y) | (x,y) <- d, not(Set.member x ns || Set.member y ns)]
                                     guard $ not(null s' && null d')
                                     return (s', d')
                     return (post sd_ps' a dfsL, pre sd a dfsR)
            <|>  do  rsL <- groupL1BsBySdA rs
                     Node (Left (OneB _ ns sigma_d sd@(sigma,delta) a _)) rsR <- rsL
                     let  rss' = [rs' | Node _ rs' <- rsR]
                          x = head . getCtx . fromEither . rootLabel . head $ head rss'
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     -- guard . not . null $ dfsL
                     let sd_qs = sdMatchingActB a (right1Bs rs)
                         sd_qs' = do (s, d) <-sd_qs
                                     let s' = s List.\\ sigma
                                         d' = [(x,y) | (x,y) <- d, not(Set.member x ns || Set.member y ns)]
                                     guard $ not(null s' && null d')
                                     return (s', d')
                     return (preB sd a x dfsL, postB sd_qs' a x dfsR)
            <|>  do  rsR <- groupR1sBySdA rs
                     Node (Right (OneB _ ns sigma_d sd@(sigma,delta) a _)) rsL <- rsR
                     let  rss' = [rs' | Node _ rs' <- rsL]
                          x = head . getCtx . fromEither . rootLabel . head $ head rss'
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     -- guard . not . null $ dfsR
                     let sd_ps = sdMatchingActB a (left1s rs)
                         sd_ps' = do (s, d) <-sd_ps
                                     let s' = s List.\\ sigma
                                         d' = [(x,y) | (x,y) <- d, not(Set.member x ns || Set.member y ns)]
                                     guard $ not(null s' && null d')
                                     return (s', d')
                     return (postB sd_ps' a x dfsL, preB sd a x dfsR)
  where
    prebase sd a = pre sd a []
    postbase sds a = post sds a []
    preBbase sd a = preB sd a (s2n "?") []
    postBbase sds a = postB sds a (s2n "?") []
    pre sd a = pre_ sd . Dia a . conj . List.nub
    post sds a fs = Box a . disj . List.nub $
       [case (sigma,delta) of  ([],[])    -> FF
                               (sigma,[]) -> diaMat sigma
                               ([],delta) -> diaDif delta
                               _          -> diaMat_ sigma $ diaDif delta | (sigma,delta)<-sds]
       ++ fs
    preB sd a x = pre_ sd . DiaB a . bind x . conj . List.nub
    postB sds a x fs = BoxB a . bind x . disj . List.nub $
       [case (sigma,delta) of  ([],[])    -> FF
                               (sigma,[]) -> diaMat sigma
                               ([],delta) -> diaDif delta
                               _          -> diaMat_ sigma $ diaDif delta | (sigma,delta)<-sds]
       ++ fs
    pre_ (sigma,delta) = boxMat sigma . boxDif delta
    boxDif  [] = id; boxDif  delta = BoxDif [(Var x,Var y) | (x,y)<-delta]
    diaDif  [] = FF; diaDif  delta = DiaDif [(Var x,Var y) | (x,y)<-delta] TT
    diaDif_ [] = id; diaDif_ delta = DiaDif [(Var x,Var y) | (x,y)<-delta]
    boxMat  [] = id; boxMat  sigma = BoxMat [(Var x,Var y) | (x,y)<-sigma]
    diaMat  [] = FF; diaMat  sigma = DiaMat [(Var x,Var y) | (x,y)<-sigma] TT
    diaMat_ [] = id; diaMat_ sigma = DiaMat [(Var x,Var y) | (x,y)<-sigma]
    right1s  rs = [log | Node (Right  log@One{}) _ <- rs]
    left1s   rs = [log | Node (Left   log@One{}) _ <- rs]
    right1Bs  rs = [log | Node (Right  log@OneB{}) _ <- rs]
    left1Bs   rs = [log | Node (Left   log@OneB{}) _ <- rs]
    getCtx (One   nctx _ _ _ _ _)  = nctx; getCtx (OneB  nctx _ _ _ _ _) = nctx
    fromEither (Left   t) = t; fromEither (Right  t) = t
    groupL1sBySdA = List.groupBy (\(Node(Left(One _ _ _ sd a _))_) (Node(Left(One _ _ _ sd' a' _))_) -> sd==sd && a==a')
                  . filter (\n -> case n of { Node(Left One{})_ -> True; _ -> False })
    groupR1sBySdA = List.groupBy (\(Node(Right(One _ _ _ sd a _))_) (Node(Right(One _ _ _ sd' a' _))_) -> sd==sd && a==a')
                  . filter (\n -> case n of { Node(Right One{})_ -> True; _ -> False })
    groupL1BsBySdA = List.groupBy (\(Node(Left(One _ _ _ sd a _))_) (Node(Left(One _ _ _ sd' a' _))_) -> sd==sd && a==a')
                   . filter (\n -> case n of { Node(Left OneB{})_ -> True; _ -> False })
    groupR1BsBySdA = List.groupBy (\(Node(Right(One _ _ _ sd a _))_) (Node(Right(One _ _ _ sd' a' _))_) -> sd==sd && a==a')
                   . filter (\n -> case n of { Node(Right OneB{})_ -> True; _ -> False })


reachableFrom (sigma',delta') (sigma,delta) =
   null(sigma List.\\ sigma') && null(delta List.\\ delta')

sdMatchingAct :: Act -> [StepLog] -> [(EqC,EqC)]
sdMatchingAct a logs = List.nub $
  do  One nctx ns sigma_d sd@(sigma,delta) a' _ <-logs
      let sigmaSubs = subs nctx (sigma_d++sigma)
      guard $ sigmaSubs a == sigmaSubs a'  ;  return sd -- (sigma_d++sigma,delta)

sdMatchingActB :: ActB -> [StepLog] -> [(EqC,EqC)]
sdMatchingActB a logs = List.nub $
  do  OneB nctx ns sigma_d sd@(sigma,delta) a' _ <-logs
      let sigmaSubs = subs nctx (sigma_d++sigma)
      guard $ sigmaSubs a == sigmaSubs a'  ;  return sd -- (sigma_d++sigma,delta)
