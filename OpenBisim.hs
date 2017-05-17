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
forest2df :: [Tree (Either StepLog StepLog)] -> [(Form,Form)] {-"\hspace{10ex}"-}
forest2df rs
            =    do  Node (Left (One _ sigma_p a _)) [] <- rs
                     let formL = prebase sigma_p a
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (formL, postbase sigmaqs a)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
            <|>  do  Node (Left (OneB _ sigma_p a _)) [] <- rs
                     let formL = preBbase sigma_p a
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (formL, postBbase sigmaqs a)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
            <|>  do  Node (Left (One _ sigma_p a _)) rsR <- rs
                     let rss' = [rs' | Node _ rs' <- rsR]
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingAct a (right1s rs)
                     return (pre sigma_p a dfsL, post sigmaqs a dfsR)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
            <|>  do  Node (Left (OneB nctx sigma_p a _)) rsR <- rs
                     let  rss' = [rs' | Node _ rs' <- rsR]
                          x = quan2nm . head . getCtx . fromEither
                            . rootLabel . head $ head rss'
                     (dfsL,dfsR) <- unzip <$> sequence (forest2df <$> rss')
                     guard . not . null $ dfsL
                     let sigmaqs = subsMatchingActB a (right1Bs rs)
                     return (preB sigma_p a x dfsL, postB sigmaqs a x dfsR)
            <|>  {-"\mathbf{do}~\ldots"-} -- do block symmetric to above omitted
  where
    prebase sigma a = pre sigma a []
    postbase subs a = post subs a []
    preBbase sigma a = preB sigma a (s2n "?") []
    postBbase subs a = postB subs a (s2n "?") []
    pre sigma a = boxMat sigma . Dia a . conj
    post subs a fs = Box a . disj $ {-"\,"-} (diaMat<$>subs) ++ fs
    preB sigma a x = boxMat sigma . DiaB a . bind x . conj
    postB subs a x fs = BoxB a . bind x . disj $ {-"\,"-} (diaMat<$>subs) ++ fs
    boxMat  [] = id
    boxMat  sigma = BoxMatch [(Var x,Var y) | (x,y)<-sigma]
    diaMat  [] = FF
    diaMat  sigma = DiaMatch [(Var x,Var y) | (x,y)<-sigma] TT
    right1s  rs = [log | Node (Right  log@(One{})) _ <- rs]
    left1s   rs = [log | Node (Left   log@(One{})) _ <- rs]
    right1Bs  rs = [log | Node (Right  log@(OneB{})) _ <- rs]
    left1Bs   rs = [log | Node (Left   log@(OneB{})) _ <- rs]
    getCtx (One   nctx _ _ _)  = nctx
    getCtx (OneB  nctx _ _ _) = nctx
    fromEither (Left   t) = t
    fromEither (Right  t) = t
subsMatchingAct a logs =
  do  One nctx sigma a' _ <-logs
      let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a'
      return sigmasubsMatchingActB a logs =
  do  OneB nctx sigma a' _ <-logs
      let sigmaSubs = subs nctx sigma
      guard $ sigmaSubs a == sigmaSubs a'
      return sigma