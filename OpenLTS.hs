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

type EqC = [Eqn]
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

respects :: EqC -> Ctx -> Bool
respects sigma nctx = undefined {- TODO
  all (\n -> P.rep part n == n) [n2i x | Nab x <- nctx]
  where (part, (n2i, _)) = mkPartitionFromEqC nctx sigma
-}
respects' :: EqC -> Ctx' -> Bool
respects' sigma ctx@(nctx,_,n2iMap) = undefined {- TODO
  all (\x -> sigma) [x | Nab x <- nctx]
  where (part,(n2i,i2n)) = mkPartitionFromEqC' ctx sigma
-}

respects_ :: EqC' -> Ctx' -> Bool
respects_ sigma ctx@(nctx,_,n2iMap) = undefined {- TODO
  all (\n -> P.rep sigma n == n) [n2i x | Nab x <- nctx]
  where (n2i,i2n) = mkMapFunsFromEqC' ctx sigma
  -}

subs_ :: Subst Tm b => Ctx' -> EqC' -> b -> b
subs_ ctx@(nctx,maxVal,n2iMap) sigma = substs $ toList sigma

joinParts sigma_p sigma_q = undefined -- TODO join two substition mappings

part2eqc ctx@(nctx,maxVal,n2iMap) sigma = [V x `Eq` t | (x,t) <- toList sigma]

one_ :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(Act,Pr))
one_ ctx  (Out x y p)   = return (emptyMap, (Up x y, p))
one_ ctx  (TauP p)      = return (emptyMap, (Tau, p))
one_ ctx  (Match t1 t2 p)
  | t1 == t2  = one_ ctx p
  | otherwise =
     do  sigma_t1t2 <- uni ([Eq t1 t2],emptyMap)
         guard $ sigma_t1t2 `respects_` ctx
         (sigma, r) <- one_ ctx p
         sigma' <- uni ([Eq t1 t2],sigma)
         guard $ sigma' `respects_` ctx
         return (sigma', r)
one_ ctx  (Plus p q) = one_ ctx p <|> one_ ctx q
one_ ctx  (Par p q)
  =    do  (sigma,(l,p')) <- one_ ctx p;  return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one_ ctx q;  return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- one_b ctx p;  (sigma_q,(lq,bq)) <- one_b ctx q
           case (lp, lq) of             -- close
             (DnB x,UpB x')  -> do  (y, q', p') <-  unbind2' bq bp
                                    sigma' <- uni ([Eq x x'], joinParts sigma_p sigma_q)
                                    guard $ sigma' `respects_` ctx
                                    return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB x',DnB x)  -> do  (y, p', q') <- unbind2' bp bq
                                    sigma' <- uni ([Eq x x'], joinParts sigma_p sigma_q)
                                    guard $ sigma' `respects_` ctx
                                    return (sigma', (Tau, Nu(y.\Par p' q')))
             _               -> empty
  <|>  do  (sigma_p, (Up x v, p')) <- one_ ctx p
           (sigma_q, (DnB x', bq)) <- one_b ctx q;  (y, q') <- unbind bq
           sigma' <- uni ([Eq x x'] ,joinParts sigma_p sigma_q)
           guard $ sigma' `respects_` ctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  do  (sigma_p, (DnB x', (y, p')))   <- one_b'  ctx p
           (sigma_q, (Up x v,     q'))    <- one_    ctx q
           sigma' <- uni ([Eq x x'] ,joinParts sigma_p sigma_q)
           guard $ sigma' `respects_` ctx
           return (sigma', (Tau, Par (subst y v p') q'))
one_ ctx (Nu b) = do  (x,p) <- unbind b;              let ctx' = extend (Nab x) ctx
                      (sigma,(l,p')) <- one_ ctx' p;  let sigmaSubs = subs_ ctx' sigma
                      case l of  Up (V x') (V y)  | x == sigmaSubs x'  -> empty
                                                  | x == sigmaSubs y   -> empty
                                 _                -> return (sigma, (l, Nu(x.\p')))
one_ _    _      = empty

one_b :: (Fresh m, Alternative m) => Ctx' -> Pr -> m (EqC',(ActB, PrB))
one_b ctx (In x p) = return (emptyMap, (DnB x, p))
one_b ctx (Match t1 t2 p)
  | t1 == t2  = one_b ctx p
  | otherwise =
    do  sigma_t1t2 <- uni ([Eq t1 t2],emptyMap)
        guard $ sigma_t1t2 `respects_` ctx
        (sigma, r) <- one_b ctx p
        sigma' <- uni ([Eq t1 t2],sigma)
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
