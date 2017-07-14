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
import           Data.Map.Strict         (Map (..), fromList, insert, (!))
import           Data.Partition          hiding (empty, rep)
import qualified Data.Partition          as P
import           PiCalc
import           Unbound.LocallyNameless hiding (GT, empty)
{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

type EqC = [(Nm,Nm)]
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
type EqC' = Partition Int

toCtx' :: Ctx -> Ctx'
toCtx' nctx = (nctx, maxVal, n2iMap)
  where
    revns = reverse (fv nctx)
    n2iMap = fromList $ zip revns [0..maxVal]
    maxVal = length nctx - 1

extend :: Quan -> Ctx' -> Ctx'
extend q (nctx, n, n2iMap) = (q:nctx, n+1, insert (quan2nm q) n n2iMap)

respects :: EqC -> Ctx -> Bool
respects sigma nctx = all (\n -> P.rep part n == n) [n2i x | Nab x <- nctx]
  where (part, (n2i, _)) = mkPartitionFromEqC nctx sigma

respects' :: EqC -> Ctx' -> Bool
respects' sigma ctx@(nctx,_,n2iMap) =
  all (\n -> P.rep part n == n) [n2i x | Nab x <- nctx]
  where (part,(n2i,i2n)) = mkPartitionFromEqC' ctx sigma

respects_ :: EqC' -> Ctx' -> Bool
respects_ sigma ctx@(nctx,_,n2iMap) =
  all (\n -> P.rep sigma n == n) [n2i x | Nab x <- nctx]
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma

subs :: Subst Tm b => Ctx -> EqC -> b -> b
subs nctx sigma = substs [(x,V y) | (x,y)<-sigma']
  where  sigma' = [(i2n i, i2n $ P.rep part i) | i<-[0..maxVal]]
         (part, (n2i, i2n)) = mkPartitionFromEqC nctx sigma
         maxVal = length nctx - 1

subs_ :: Subst Tm b => Ctx' -> EqC' -> b -> b
subs_ ctx@(nctx,maxVal,n2iMap) sigma = substs [(x,V y) | (x,y)<-sigma']
  where  sigma' = [(i2n i, i2n $ P.rep sigma i) | i<-[0..maxVal]]
         (n2i, i2n) = mkMapFunsFromEqC' ctx sigma

mkPartitionFromEqC ::  Ctx -> EqC -> (Partition Int, (Nm -> Int, Int -> Nm))
mkPartitionFromEqC nctx sigma = (part, (n2i, i2n))
  where
    part =  foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- sigma] discrete
    i2n i = revns !! i
    n2i x = n2iMap ! x
    revns = reverse (fv nctx)
    n2iMap = fromList $ zip revns [0..maxVal]
    maxVal = length nctx - 1

mkPartitionFromEqC' :: Ctx' -> EqC -> (Partition Int, (Nm -> Int, Int -> Nm))
mkPartitionFromEqC' (nctx,maxVal,n2iMap) sigma = (part, (n2i, i2n))
  where
    part =  foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- sigma] discrete
    i2n i = quan2nm $ nctx !! (maxVal - i)
    n2i x = n2iMap ! x

joinNm ctx (x,y) sigma = joinElems (n2i x) (n2i y) sigma
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma

joinParts sigma_p sigma_q = fromSets $ nontrivialSets sigma_p ++ nontrivialSets sigma_q

mkMapFunsFromEqC' :: Ctx' -> EqC' -> (Nm -> Int, Int -> Nm)
mkMapFunsFromEqC' (nctx,maxVal,n2iMap) sigma = (n2i, i2n)
  where
    i2n i = quan2nm $ nctx !! (maxVal - i)
    n2i x = n2iMap ! x

part2eqc :: Ctx' -> EqC' -> EqC
part2eqc ctx@(nctx,maxVal,n2iMap) sigma =
  [(i2n i, i2n j) | (i,j) <- [(i, P.rep sigma i) | i<-[0..maxVal]], i/=j]
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma

one_ :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(Act,Pr))
one_ ctx  (Out x y p)   = return (P.empty, (Up x y, p))
one_ ctx  (TauP p)      = return (P.empty, (Tau, p))
one_ ctx  (Match (V x) (V y) p)  | x == y                   = one_ ctx p
                                     | [(x,y)] `respects'` ctx  =
                                           do  (sigma, r) <- one_ ctx p
                                               let sigma' = joinNm ctx (x,y) sigma
                                               guard $ sigma' `respects_` ctx
                                               return (sigma', r)
one_ ctx  (Plus p q) = one_ ctx p <|> one_ ctx q
one_ ctx  (Par p q)
  =    do  (sigma,(l,p')) <- one_ ctx p;  return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one_ ctx q;  return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- one_b ctx p;  (sigma_q,(lq,bq)) <- one_b ctx q
           case (lp, lq) of             -- close
             (DnB(V x),UpB(V x'))  -> do  (y, q', p') <-  unbind2' bq bp
                                          let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
                                          guard $ sigma' `respects_` ctx
                                          return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB(V x'),DnB(V x))  -> do  (y, p', q') <- unbind2' bp bq
                                          let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
                                          guard $ sigma' `respects_` ctx
                                          return (sigma', (Tau, Nu(y.\Par p' q')))
             _                     -> empty
  <|>  do  (sigma_p, (Up (V x) v, p')) <- one_ ctx p
           (sigma_q, (DnB (V x'), bq)) <- one_b ctx q;  (y, q') <- unbind bq
           let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
           guard $ sigma' `respects_` ctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  do  (sigma_p, (DnB (V x'), (y, p')))   <- one_b'  ctx p
           (sigma_q, (Up (V x) v,     q'))    <- one_    ctx q
           let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
           guard $ sigma' `respects_` ctx
           return (sigma', (Tau, Par (subst y v p') q'))
one_ ctx (Nu b) = do  (x,p) <- unbind b;              let ctx' = extend (Nab x) ctx
                      (sigma,(l,p')) <- one_ ctx' p;  let sigmaSubs = subs_ ctx' sigma
                      case l of  Up (V x') (V y)  | x == sigmaSubs x'  -> empty
                                                      | x == sigmaSubs y   -> empty
                                 _                    -> return (sigma, (l, Nu(x.\p')))
one_ _    _      = empty

one_b :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(ActB, PrB))
one_b ctx (In x p) = return (P.empty, (DnB x, p))
one_b ctx (Match (V x) (V y) p)  | x == y                   = one_b ctx p
                                     | [(x,y)] `respects'` ctx  =
                                           do  (sigma, r) <- one_b ctx p
                                               let sigma' = joinNm ctx (x,y) sigma
                                               guard $ sigma' `respects_` ctx
                                               return (sigma', r)
one_b ctx (Plus p q) = one_b ctx p <|> one_b ctx q
one_b ctx (Par p q) =
       do (sigma,(l,(x,p'))) <- one_b' ctx p;  return (sigma,(l, x.\Par p' q))
  <|>  do (sigma,(l,(x,q'))) <- one_b' ctx q;  return (sigma,(l, x.\Par p q'))
one_b ctx (Nu b)  =    do  (x,p) <- unbind b;                    let ctx' = extend (Nab x) ctx
                           (sigma,(l,(y,p'))) <- one_b' ctx' p;  let sigmaSubs = subs_ ctx' sigma
                           case l of  UpB (V x')  | x == sigmaSubs x' -> empty
                                      DnB (V x')  | x == sigmaSubs x' -> empty
                                      _             -> return (sigma, (l, y.\Nu (x.\p')))
                  <|>  do  (x,p) <- unbind b;                          let ctx' = extend (Nab x) ctx
                           (sigma,(Up y (V x'),p')) <- one_ ctx' p;  let sigmaSubs = subs_ ctx' sigma
                           guard $ x == sigmaSubs x' && V x /= sigmaSubs y
                           return (sigma, (UpB y, x.\p')) -- open
one_b _    _ = empty

one_b' ctx p = do (sigma,(l,b)) <- one_b ctx p; r <- unbind b; return (sigma,(l,r))
