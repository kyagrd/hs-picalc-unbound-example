{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module OpenLTS where
import           Control.Applicative
import           Control.Monad
import           Data.Map.Strict         (Map (..), fromList, insert, toList,
                                          (!))
-- import           Data.Partition          hiding (empty, rep)
-- import qualified Data.Partition          as P
import           PiCalc
import           Unbound.LocallyNameless hiding (GT, empty, toList)
{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

type EqC = [(Tm,Tm)]
{-
infixr 5 .:
(.:) :: (Nm,Nm) -> EqC -> EqC
(x,y) .: sigma = case compare x y of  LT -> [(x,y)] .++ sigma
                                      EQ -> sigma
                                      GT -> [(y,x)] .++ sigma
infixr 5 .++
(.++) = union
-}

type Ctx = [Quan]
data Quan = All Nm | Nab Nm deriving (Eq, Ord, Show)
quan2nm :: Quan -> Nm
quan2nm (All x) = x
quan2nm (Nab x) = x

$(derive [''Quan])
instance Alpha Quan
instance Subst Tm Quan


-- wrapper -------------------
one nctx p = do (sigma, r) <- one_ ctx p
                return (part2eqc ctx sigma, r)
  where ctx = toCtx' nctx
oneb nctx b = do (sigma, r) <- one_b ctx b
                 return (part2eqc ctx sigma, r)
  where ctx = toCtx' nctx
-----------------------------

type Ctx' = (Ctx, Int, Map Nm Int)
emptyCtx' = ([], 0, fromList [])
type EqC' = Map Nm Tm -- unifier as substitution mapping

toCtx' :: Ctx -> Ctx'
toCtx' nctx = (nctx, maxVal, n2iMap)
  where
    revns = reverse (fv nctx)
    n2iMap = fromList $ zip revns [0..maxVal]
    maxVal = length nctx - 1

extend :: Quan -> Ctx' -> Ctx'
extend q (nctx, n, n2iMap) = (q:nctx, n+1, insert (quan2nm q) n n2iMap)

respects :: EqC' -> Ctx' -> Bool
respects sigma ctx@(nctx,_,n2iMap) =
  all nab [(x,expand sigma (V x)) | Nab x <- nctx]
  where
     n2i k = n2iMap!k
     nab (x, V y) = n2i x <= n2i y
     nab _        = False

subs_ :: Subst Tm b => Ctx' -> EqC' -> b -> b
subs_ ctx@(nctx,maxVal,n2iMap) sigma = substs $ toList sigma

joinParts sigma = uni [(V x,t) | (x,t) <- toList sigma]

part2eqc ctx@(nctx,maxVal,n2iMap) sigma = [(V x, t) | (x,t) <- toList sigma]

-- TODO expand whenever making a new binding using (.\) or bind

one_ :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(Act,Pr))
one_ ctx  (Out x y p)   = return (emptyMap, (Up x y, p))
one_ ctx  (TauP p)      = return (emptyMap, (Tau, p))
one_ ctx  (Match t1 t2 p) | t1 == t2  = one_ ctx p
                          | otherwise = do  sigma_t1t2 <- uni [(t1,t2)] emptyMap
                                            guard $ sigma_t1t2 `respects` ctx
                                            (sigma, r) <- one_ ctx p
                                            sigma' <- uni [(t1,t2)] sigma
                                            guard $ sigma' `respects` ctx
                                            return (sigma', r)
one_ ctx  (Plus p q) = one_ ctx p <|> one_ ctx q
one_ ctx  (Par p q)
  =    do  (sigma,(l,p')) <- one_ ctx p;  return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one_ ctx q;  return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- one_b ctx p;  (sigma_q,(lq,bq)) <- one_b ctx q
           case (lp, lq) of             -- close
             (DnB x,UpB x')  -> do  (y, q', p') <-  unbind2' bq bp
                                    sigma' <- uni [(x,x')] =<< joinParts sigma_p sigma_q
                                    guard $ sigma' `respects` ctx
                                    return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB x',DnB x)  -> do  (y, p', q') <- unbind2' bp bq
                                    sigma' <- uni [(x,x')] =<< joinParts sigma_p sigma_q
                                    guard $ sigma' `respects` ctx
                                    return (sigma', (Tau, Nu(y.\Par p' q')))
             _               -> empty
  <|>  do  (sigma_p, (Up x v, p')) <- one_ ctx p
           (sigma_q, (DnB x', bq)) <- one_b ctx q;  (y, q') <- unbind bq
           sigma' <- uni [(x,x')] =<< joinParts sigma_p sigma_q
           guard $ sigma' `respects` ctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  do  (sigma_p, (DnB x', (y, p')))   <- one_b'  ctx p
           (sigma_q, (Up x v,     q'))    <- one_    ctx q
           sigma' <- uni [(x,x')] =<< joinParts sigma_p sigma_q
           guard $ sigma' `respects` ctx
           return (sigma', (Tau, Par (subst y v p') q'))
one_ ctx (Nu b) = do  (x,p) <- unbind b; let ctx' = extend (Nab x) ctx
                      (sigma,(l,p')) <- one_ ctx' p
                      case l of  Up _ _ | x `elem` (fv l :: [Nm]) -> empty
                                 _      -> return (sigma, (l, Nu(x.\p')))
one_ _    _      = empty

one_b :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(ActB, PrB))
one_b ctx (In x p) = return (emptyMap, (DnB x, p))
one_b ctx (Match t1 t2 p) | t1 == t2  = one_b ctx p
                          | otherwise = do  sigma_t1t2 <- uni [(t1,t2)] emptyMap
                                            guard $ sigma_t1t2 `respects` ctx
                                            (sigma, r) <- one_b ctx p
                                            sigma' <- uni [(t1,t2)] sigma
                                            guard $ sigma' `respects` ctx
                                            return (sigma', r)
one_b ctx (Plus p q) = one_b ctx p <|> one_b ctx q
one_b ctx (Par p q)
  =    do (sigma,(l,(x,p'))) <- one_b' ctx p;  return (sigma,(l, x.\Par p' q))
  <|>  do (sigma,(l,(x,q'))) <- one_b' ctx q;  return (sigma,(l, x.\Par p q'))
one_b ctx (Nu b)
  =    do  (x,p) <- unbind b;       let ctx' = extend (Nab x) ctx
           (sigma,(l,(y,p'))) <- one_b' ctx' p
           case l of  UpB x'  | x `notElem` (fv $ expand sigma x' :: [Nm]) -> empty
                      DnB x'  | x `notElem` (fv $ expand sigma x' :: [Nm]) -> empty
                      _           -> return (sigma, (l, y.\Nu (x.\p')))
  <|>  do  (x,p) <- unbind b
           let ctx' = extend (Nab x) ctx
           (sigma,(Up y x',p')) <- one_ ctx' p
           guard $ x `elem` (fv $ expand sigma x' :: [Nm])
           guard $ x `notElem` (fv $ expand sigma y :: [Nm])
           return (sigma, (UpB y, x.\p')) -- open
one_b _    _ = empty

one_b' ctx p = do (sigma,(l,b)) <- one_b ctx p; r <- unbind b; return (sigma,(l,r))
