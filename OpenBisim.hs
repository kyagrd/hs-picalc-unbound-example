{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module OpenBisim where
import           Control.Applicative
import           Control.Monad
import           Data.Tree
import qualified IdSubLTS
import           OpenLTS
import           PiCalc
import           Unbound.LocallyNameless hiding (empty)

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
                        let x' = runFreshM $ freshFrom (fv nctx) bp'
                        return . (or :: [Bool] -> Bool) . runFreshMT $ do
                          (lq, bq') <-IdSubLTS.oneb (sigmaSubs q)
                          guard $ lp == lq
                          (x, q1, p1) <- unbind2' bq' bp'
                          let (p', q')  | x == x'    = (p1, q1)
                                        | otherwise  = subst x ((Var x')) (p1, q1)
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
                           let x' = runFreshM $ freshFrom (fv nctx) bp'
                           returnL (OneB nctx sigma lp bp') . runFreshMT $ do
                             (lq, bq') <-IdSubLTS.oneb (sigmaSubs q)
                             guard $ lp == lq
                             (x, p1, q1) <- unbind2' bp' bq'
                             let (p', q')   | x == x'    = (p1, q1)
                                            | otherwise  = subst x ((Var x')) (p1, q1)
                             let nctx' = case lp of   DnB _ -> All x' : nctx
                                                      UpB _ -> Nab x' : nctx
                             returnR (OneB nctx sigma lq bq') $ sim' nctx' p' q'

freshFrom :: Fresh m => [Nm] -> PrB -> m Nm
freshFrom xs b = do { mapM_ fresh xs; (y,_) <- unbind b; return y }

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
     let x' = runFreshM $ freshFrom (fv nctx) bp' -- to use same new quan var
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
     let x' = runFreshM $ freshFrom (fv nctx) bq' -- to use same new quan var
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
     let x' = runFreshM $ freshFrom (fv nctx) bp' -- to use same new quan var
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
     let x' = runFreshM $ freshFrom (fv nctx) bq' -- to use same new quan var
     returnR (OneB nctx sigma lq bq') . runFreshMT $ do
       (lp, bp') <-IdSubLTS.oneb (subs nctx sigma p) -- follow with same sub and label
       guard $ lp == lq
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       returnL (OneB nctx sigma lp bp') $ bisim' nctx' p' q'
forest2df :: [Tree (Either StepLog StepLog)] -> [(Form,Form)]
forest2df rs
            =    do  Node (Left (One _ sigma_p a _)) [] <- rs
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (prebase sigma_p a, postbase sigmaqs a)
            <|>  do  Node (Right (One _ sigma_q a _)) [] <- rs
                     let formR = prebase sigma_q a
                     let sigmaps = subsMatchingAct a (left1s rs)
                     return (postbase sigmaps a, formR)
            <|>  do  Node (Left (OneB _ sigma_p a _)) [] <- rs
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (preBbase sigma_p a, postBbase sigmaqs a)
            <|>  do  Node (Right (OneB _ sigma_q a _)) [] <- rs
                     let formR = preBbase sigma_q a
                     let sigmaps = subsMatchingActB a (left1Bs rs)
                     return (postBbase sigmaps a, formR)
            <|>  do  Node (Left (One _ sigma_p a _)) rsR <- rs
                     let rss' = [rs' | Node _ rs' <- rsR]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (pre sigma_p a dfsL, post sigmaqs a dfsR)
            <|>  do  Node (Right (One _ sigma_q a _)) rsL <- rs
                     let rss' = [rs' | Node _ rs' <- rsL]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaps = subsMatchingAct a (left1s rs)
                     return (post sigmaps a dfsL, pre sigma_q a dfsR)
            <|>  do  Node (Left (OneB nctx sigma_p a _)) rsR <- rs
                     let  rss' = [rs' | Node _ rs' <- rsR]
                          x = quan2nm . head . getCtx . fromEither
                            . rootLabel . head $ head rss'
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (preB sigma_p a x dfsL, postB sigmaqs a x dfsR)
            <|>  do  Node (Right (OneB nctx sigma_q a _)) rsL <- rs
                     let  rss' = [rs' | Node _ rs' <- rsL]
                          x = quan2nm . head . getCtx . fromEither . rootLabel
                                $ head (head rss')
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaps = subsMatchingActB a (left1Bs rs)
                     return (postB sigmaps a x dfsL, preB sigma_q a x dfsR)
  where
    prebase sigma a = pre sigma a []
    postbase sigmas a = post sigmas a []
    preBbase sigma a = preB sigma a (s2n "?") []
    postBbase sigmas a = postB sigmas a (s2n "?") []
    pre sigma a = boxMat sigma . Dia a . conj
    post sigmas a fs = Box a . disj $  (diaMat<$>sigmas) ++ fs
    preB sigma a x = boxMat sigma . DiaB a . bind x . conj
    postB sigmas a x fs = BoxB a . bind x . disj $  (diaMat<$>sigmas) ++ fs
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
  do  One nctx sigma a' _ <-logs          ;  let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a' ;  return sigma

subsMatchingActB :: ActB -> [StepLog] -> [EqC]
subsMatchingActB a logs =
  do  OneB nctx sigma a' _ <-logs         ;  let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a' ;  return sigma
