{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module OpenLTS where
import PiCalc; import Control.Applicative; import Control.Monad
import Data.Partition hiding (empty)
import Unbound.LocallyNameless hiding (empty, rep, GT)
import Data.Map.Strict (fromList, (!))

type EqC = [(Nm,Nm)]
infixr 5 .:  (.:) :: (Nm,Nm) -> EqC -> EqC
(x,y) .: sigma = case compare x y of  LT -> [(x,y)] .++ sigma
                                      EQ -> sigma
                                      GT -> [(y,x)] .++ sigma
infixr 5 .++  (.++) = union

type Ctx = [Quan]
data Quan = All Nm | Nab Nm deriving (Eq, Ord, Show)
quan2nm :: Quan -> Nm;  quan2nm (Nab x)  = x

respects :: EqC -> Ctx -> Bool
respects sigma nctx = all (\n -> rep part n == n) [n2i x | Nab x <- nctx]
  where (part, (n2i, _)) = mkPartitionFromEqC nctx sigma

subs :: Subst Tm b => Ctx -> EqC -> b -> b
subs nctx sigma = foldr (.) id [subst x ((Vary)) | (x,y)<-sigma']
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
  =    do  (sigma,(l,p')) <- one nctx p;  return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one nctx q;  return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- oneb nctx p;  (sigma_q,(lq,bq)) <- oneb nctx q
           case (lp, lq) of             -- close
             (DnB(Var x),UpB(Var x'))  -> do  (y, q', p') <-  unbind2' bq bp
                                              let sigma' = (x,x') .: sigma_p .++ sigma_q
                                              guard $ sigma' `respects` nctx
                                              return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB(Var x'),DnB(Var x))  -> do  (y, p', q') <- unbind2' bp bq
                                              let sigma' = (x,x') .: sigma_p .++ sigma_q
                                              guard $ sigma' `respects` nctx
                                              return (sigma', (Tau, Nu(y.\Par p' q')))
             _                         -> empty
  <|>  do  (sigma_p, (Up (Var x) v, p')) <- one nctx p
           (sigma_q, (DnB (Var x'), bq)) <- oneb nctx q;  (y, q') <- unbind bq
           let sigma' = (x,x') .: sigma_p .++ sigma_q
           guard $ sigma' `respects` nctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  do  (sigma_p, (DnB (Var x'), (y,  p')))   <- oneb'  nctx p
           (sigma_q, (Up (Var x) v,     q'))    <- one    nctx q
           let sigma' = (x,x') .: sigma_p .++ sigma_q
           guard $ sigma' `respects` nctx
           return (sigma', (Tau, Par (subst y v p') q'))
one nctx (Nu b) = do  (x,p) <- unbind b;              let nctx' = Nab x : nctx
                      (sigma,(l,p')) <- one nctx' p;  let sigmaSubs = subs nctx' sigma
                      case l of  Up (Var x') (Var y)  | x == sigmaSubs x'  -> empty
                                                      | x == sigmaSubs y   -> empty
                                 _                    -> return (sigma, (l, Nu(x.\p')))
one _    _      = empty

oneb :: (Fresh m, Alternative m) => Ctx -> Pr -> m (EqC,(ActB, PrB))
oneb nctx (In x p) = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)  | x == y                   = oneb nctx p
                                     | [(x,y)] `respects` nctx  =
                                           do  (sigma, r) <- oneb nctx p
                                               let sigma' = (x,y) .: sigma
                                               guard $ sigma' `respects` nctx
                                               return (sigma', r)
oneb nctx (Plus p q) = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q) = 
       do (sigma,(l,(x,p'))) <- oneb' nctx p;  return (sigma,(l, x.\Par p' q))
  <|>  do (sigma,(l,(x,q'))) <- oneb' nctx q;  return (sigma,(l, x.\Par p q'))
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

