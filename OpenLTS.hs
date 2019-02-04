{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module OpenLTS where

import           Control.Applicative
import           Data.Foldable (asum)
import           Control.Monad
import           Data.Map.Strict                 (Map (..), fromList, insert,
                                                  (!))
import           Data.Partition                  hiding (empty, rep)
import qualified Data.Partition                  as P
import qualified Data.Set                        as Set
import           Debug.Trace
import qualified IdSubLTS
import           PiCalc
import           Unbound.LocallyNameless         hiding (GT, empty)
{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

type NmSet = Set.Set Nm

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

type Ctx = [Nm]

-- wrapper -------------------
one nctx ns p = do ((sigma,delta), r) <- one_ ctx ns p
                   return ((part2eqc ctx sigma,delta), r)
  where ctx = toCtx' nctx
oneb nctx ns b = do ((sigma,delta), r) <- one_b ctx ns b
                    return ((part2eqc ctx sigma,delta), r)
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

extend :: Nm -> Ctx' -> Ctx'
extend q (nctx, n, n2iMap) = (q:nctx, n+1, insert q (n+1) n2iMap)

respects :: EqC -> Ctx -> NmSet -> Bool
respects sigma nctx ns =
  -- all (\n -> P.rep part n == n && Set.member (i2n n) ns) [n2i x | Nab x <- nctx]
  and [P.rep part (n2i x) /= P.rep part (n2i y) | x<-Set.toList ns, y<-Set.toList ns, x/=y]
  where (part, (n2i, i2n)) = mkPartitionFromEqC nctx sigma

respects' :: EqC -> Ctx' -> NmSet -> Bool
respects' sigma ctx@(nctx,_,n2iMap) ns =
  -- all (\n -> P.rep part n == n && Set.member (i2n n) ns) [n2i x | Nab x <- nctx]
  and [P.rep part (n2i x) /= P.rep part (n2i y) | x<-Set.toList ns, y<-Set.toList ns, x/=y]
  where (part, (n2i,i2n)) = mkPartitionFromEqC' ctx sigma

respects_ :: EqC' -> Ctx' -> NmSet -> Bool
respects_ sigma ctx@(nctx,_,n2iMap) ns =
  -- all (\n -> P.rep sigma n == n && Set.member (i2n n) ns) [n2i x | Nab x <- nctx]
  and [P.rep part (n2i x) /= P.rep part (n2i y) | x<-Set.toList ns, y<-Set.toList ns, x/=y]
  where (part, (n2i,i2n)) = (sigma, mkMapFunsFromEqC' ctx sigma)

subs :: Subst Tm b => Ctx -> EqC -> b -> b
subs nctx sigma = substs [(x,Var y) | (x,y)<-sigma']
  where  sigma' = [(i2n i, i2n $ P.rep part i) | i<-[0..maxVal]]
         (part, (n2i, i2n)) = mkPartitionFromEqC nctx sigma
         maxVal = length nctx - 1

subs_ :: Subst Tm b => Ctx' -> EqC' -> b -> b
subs_ ctx@(nctx,maxVal,n2iMap) sigma = substs [(x,Var y) | (x,y)<-sigma']
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
    i2n i = nctx !! (maxVal - i)
    n2i x = n2iMap ! x

joinNm ctx (x,y) sigma = joinElems (n2i x) (n2i y) sigma
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma

joinParts sigma_p sigma_q = fromSets $ nontrivialSets sigma_p ++ nontrivialSets sigma_q

mkMapFunsFromEqC' :: Ctx' -> EqC' -> (Nm -> Int, Int -> Nm)
mkMapFunsFromEqC' (nctx,maxVal,n2iMap) sigma = (n2i, i2n)
  where
    i2n i = nctx !! (maxVal - i)
    n2i x = n2iMap ! x

part2eqc :: Ctx' -> EqC' -> EqC
part2eqc ctx@(nctx,maxVal,n2iMap) sigma =
  [(i2n i, i2n j) | (i,j) <- [(i, P.rep sigma i) | i<-[0..maxVal]], i/=j]
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma

eqcVars = map (\(x,y) -> (Var x,Var y))

one_ :: (Fresh m, Alternative m) => Ctx' -> NmSet -> Pr -> m ((EqC',EqC),(Act,Pr))
one_ ctx _  (Out x y p)   = return ((P.empty,[]), (Up x y, p))
one_ ctx ns (In x b)      =
  do  (z,p) <- unbind b
      -- return (P.empty, (Dn x (Var z), p))
      asum [ return ((P.empty,[]), (Dn x (Var y), subst z (Var y) p))
            | y <- Set.toList(Set.insert z ns) ]
one_ ctx _  (TauP p)      = return ((P.empty,[]), (Tau, p))
one_ ctx ns pp@(Match (Var x) (Var y) p)
  | x == y                   = one_ ctx ns p
  | respects' [(x,y)] ctx ns =
      do  ((sigma,delta), r) <- one_ ctx ns p
          let sigma' = joinNm ctx (x,y) sigma;  sigmaSubs' = subs_ ctx sigma'
          guard $ all (uncurry (/=)) (sigmaSubs' $ eqcVars delta)
          return ((sigma',delta), sigmaSubs' r)
one_ ctx ns (Diff (Var x) (Var y) p)
  | x == y   = empty
  | Set.member x ns || Set.member y ns  =
                 do  ((sigma,delta), r) <- one_ ctx ns p
                     return ((sigma,(x,y):delta), r)
  | otherwise =  do  ((sigma,delta), r) <- one_ ctx ns p
                     let sigmaSubs = subs_ ctx sigma;  delta' = (x,y):delta
                     guard $ all (uncurry (/=)) (sigmaSubs $ eqcVars delta')
                     return ((sigma,delta'), r)
one_ ctx ns (Plus p q) = one_ ctx ns p <|> one_ ctx ns q
one_ ctx ns (Par p q)
  =    do  (sd,(l,p')) <- one_ ctx ns p;  return (sd,(l,Par p' q))
  <|>  do  (sd,(l,q')) <- one_ ctx ns q;  return (sd,(l,Par p q'))
  <|>  do  ((sigma_p,delta_p), (UpB x, bp)) <- one_b ctx ns p;  (z, p') <- unbind bp
           ((sigma_q,delta_q), q') <- one_In ctx ns q (Dn x (Var z))
           let sigma = joinParts sigma_p sigma_q;  delta = delta_p++delta_q
           let sigmaSubs = subs_ ctx sigma
           guard $ respects_ sigma ctx ns && all (uncurry (/=)) (sigmaSubs $ eqcVars delta)
           return ((sigma,delta_p++delta_q), (Tau, Nu(z.\Par p' q'))) -- close
  <|>  do  ((sigma_q,delta_q), (UpB x, bq)) <- one_b ctx ns q;  (z, q') <- unbind bq
           ((sigma_p,delta_p), p') <- one_In ctx ns p (Dn x (Var z))
           let sigma = joinParts sigma_p sigma_q;  delta = delta_p++delta_q
           let sigmaSubs = subs_ ctx sigma
           guard $ respects_ sigma ctx ns && all (uncurry (/=)) (sigmaSubs $ eqcVars delta)
           return ((sigma,delta), (Tau, Nu(z.\Par p' q'))) -- close
  <|>  do  ((sigma_p,delta_p), (Up (Var x) v,        p')) <- one_ ctx ns p
           ((sigma_q,delta_q), (Dn (Var x') (Var y), q')) <- one_ ctx ns q
           let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
               delta = delta_p++delta_q
           let sigmaSubs' = subs_ ctx sigma'
           guard $ respects_ sigma' ctx ns && all (uncurry (/=)) (sigmaSubs' $ eqcVars delta)
           return ((sigma',delta), (Tau, Par p' (subst y v q'))) -- interaction
  <|>  do  ((sigma_p,delta_p), (Dn (Var x') (Var y), p')) <- one_ ctx ns p
           ((sigma_q,delta_q), (Up (Var x) v,        q')) <- one_ ctx ns q
           let sigma' = joinNm ctx (x,x') (joinParts sigma_p sigma_q)
               delta = delta_p++delta_q
           let sigmaSubs' = subs_ ctx sigma'
           guard $ respects_ sigma' ctx ns && all (uncurry (/=)) (sigmaSubs' $ eqcVars delta)
           return ((sigma',delta), (Tau, Par (subst y v p') q')) -- interaction
one_ ctx ns (Nu b) =
  do  (x,p) <- unbind b
      let ctx' = extend x ctx;  ns' = Set.insert x ns
      ((sigma,delta),(l,p')) <- one_ ctx' ns' p
      guard . not $ x `elem` (fv $ part2eqc ctx' sigma :: [Nm])
      let sigmaSubs = subs_ ctx' sigma
      case l of  Up x' y  | Var x == sigmaSubs x'  -> empty
                          | Var x == sigmaSubs y   -> empty
                 Dn x' y  | Var x == sigmaSubs x'  -> empty
                          | Var x == sigmaSubs y   -> empty
                 _        -> return ((sigma,delta), (l, Nu(x.\p')))
one_ _   _  _      = empty


one_b :: (Fresh m, Alternative m) => Ctx' -> NmSet -> Pr -> m ((EqC',EqC),(ActB, PrB))
one_b ctx ns (Match (Var x) (Var y) p)
  | x == y                   = one_b ctx ns p
  | respects' [(x,y)] ctx ns =
      do  ((sigma,delta), r) <- one_b ctx ns p
          let sigma' = joinNm ctx (x,y) sigma;  sigmaSubs' = subs_ ctx sigma'
          guard $ all (uncurry (/=)) (sigmaSubs' $ eqcVars delta)
          return ((sigma',delta), sigmaSubs' r)
one_b ctx ns (Diff (Var x) (Var y) p)
  | x == y  = empty
  | Set.member x ns || Set.member y ns  =
                 do  ((sigma,delta), r) <- one_b ctx ns p
                     return ((sigma,(x,y):delta),r)
  | otherwise =  do  ((sigma,delta), r) <- one_b ctx ns p
                     let sigmaSubs = subs_ ctx sigma;  delta' = (x,y):delta
                     guard $ all (uncurry (/=)) (sigmaSubs $ eqcVars delta')
                     return ((sigma,delta'), r)
one_b ctx ns (Plus p q) = one_b ctx ns p <|> one_b ctx ns q
one_b ctx ns (Par p q) =
       do (sd,(l,(x,p'))) <- one_b' ctx ns p;  return (sd,(l, x.\Par p' q))
  <|>  do (sd,(l,(x,q'))) <- one_b' ctx ns q;  return (sd,(l, x.\Par p q'))
one_b ctx ns (Nu b) =
       do  (x,p) <- unbind b;                       let ctx' = extend x ctx
           ((sigma,delta),(l@(UpB(Var x')),(y,p'))) <- one_b' ctx' ns p
           let sigmaSubs = subs_ ctx' sigma
           guard $ x /= sigmaSubs x'
           return ((sigma,delta), (l, y.\Nu (x.\p')))
  <|>  do  (x,p) <- unbind b
           let ctx' = extend x ctx;  ns' = Set.insert x ns
           ((sigma,delta),(Up y (Var x'),p')) <- one_ ctx' ns' p
           let sigmaSubs = subs_ ctx' sigma
           guard $ x == sigmaSubs x' && Var x /= sigmaSubs y
           return ((sigma,delta), (UpB y, x.\p')) -- open
one_b _   _  _ = empty

one_b' ctx ns p = do (sd,(l,b)) <- one_b ctx ns p; r <- unbind b; return (sd,(l,r))

-- specialization of one with a specific input label
one_In :: (Fresh m, Alternative m) => Ctx' -> NmSet -> Pr -> Act -> m ((EqC',EqC),Pr)
one_In ctx ns (In (Var x) b) (Dn (Var x') y)
  | x == x'  = do (z,p) <- unbind b;  return ((P.empty,[]), subst z y p)
  | respects' [(x,x')] ctx ns =
      do (z,p) <- unbind b;  return ((joinNm ctx (x, x') P.empty,[]), subst z y p)
one_In ctx ns (Match (Var x) (Var y) p) l@(Dn _ _)
  | x == y = one_In ctx ns p l
  | respects' [(x,y)] ctx ns =
      do  ((sigma,delta), r) <- one_In ctx ns p l
          let sigma' = joinNm ctx (x,y) sigma;  sigmaSubs' = subs_ ctx sigma'
          guard $ all (uncurry (/=)) (sigmaSubs' $ eqcVars delta)
          return ((sigma',delta), r)
one_In ctx ns (Diff (Var x) (Var y) p) l@(Dn _ _)
  | x == y  = empty
  | Set.member x ns || Set.member y ns  =
                 do  ((sigma,delta), r) <- one_In ctx ns p l
                     return ((sigma,(x,y):delta),r)
  | otherwise =  do  ((sigma,delta), r) <- one_In ctx ns p l
                     let sigmaSubs = subs_ ctx sigma
                     guard $ sigmaSubs (Var x) /= sigmaSubs (Var y)
                     return ((sigma,(x,y):delta), r)
one_In ctx ns (Plus p q) l@(Dn _ _) = one_In ctx ns p l <|> one_In ctx ns q l
one_In ctx ns (Par p q) l@(Dn _ _) =
       do (sd, p') <- one_In ctx ns p l;  return (sd, Par p' q)
  <|>  do (sd, q') <- one_In ctx ns q l;  return (sd, Par p q')
one_In ctx ns (Nu b) l@(Dn _ _) =
  do  (x,p) <- unbind b
      let ctx' = extend x ctx;  ns' = Set.insert x ns
      (sd@(sigma,_), p') <- one_In ctx' ns' p l
      guard . not $ x `elem` (fv $ part2eqc ctx' sigma :: [Nm])
      return (sd, Nu(x.\p'))
one_In _  _ _ _ = empty
