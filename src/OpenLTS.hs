{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
module OpenLTS where

import           Control.Applicative
import           Control.Monad
import           Data.List               (union)
import qualified Data.Map.Strict         as Map
import           Data.Maybe
import           Data.Partition          hiding (empty)
import qualified Data.Set                as Set
import qualified LateLTS                 as L
import           PiCalc
import           Unbound.LocallyNameless hiding (GT, empty, rep, union)

import           Debug.Trace

{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

-- TOOD can nctx and unification constraint collection
-- packaged as a set of monad transformer layers?

data Quan = All NameTm | Nab NameTm deriving (Eq, Ord, Show)

q2n (All x) = x
q2n (Nab x) = x

-- names in nctx must be distinct (i.e., no  duplicates)
-- and they are in reversed order from what we usally write on paper
-- as usual for contexts represented as lists
-- that is, "forall x y z ..." would be [All z,All y,All x]

-- type synonym for the collection of equlaity constraints over names
type EqC = [(NameTm,NameTm)]

one :: (Fresh m, Alternative m) => [Quan] -> Pr -> m (EqC,(Act,Pr))
one nctx (Out x y p)   = return ([], (Up x y, p))
one nctx (TauP p)      = return ([], (Tau, p))
one nctx (Match (Var x) (Var y) p)
          | x == y    = one nctx p
          | otherwise = do (s, r) <- one nctx p
                           let s' = (x,y) .: s
                           guard $ s' `respects` nctx
                           return (s', r)
one nctx (Plus p q) = one nctx p <|> one nctx q
one nctx (Par p q)
   = do { (s,(l,p')) <- one nctx p; return (s,(l,Par p' q)) }
 <|> do { (s,(l,q')) <- one nctx q; return (s,(l,Par p q')) }
 <|> do (sp,(lp,bp)) <- oneb nctx p
        (sq,(lq,bq)) <- oneb nctx q
        case (lp, lq) of
          (DnB (Var x), UpB (Var y))
            -> do (v, q', p') <-  unbind2' bq bp
                  let s' = (x,y) .: sp .++ sq
                  guard $ s' `respects` nctx
                  return (s', (Tau, Nu(v.\Par p' q'))) -- close
          (UpB (Var x), DnB (Var y))
            -> do (v, p', q') <- unbind2' bp bq
                  let s' = (x,y) .: sp .++ sq
                  guard $ s' `respects` nctx
                  return (s', (Tau, Nu(v.\Par p' q'))) -- close
          _ -> empty
 <|> do (sp, (DnB (Var x), bp)) <- oneb nctx p
        (sq, (Up (Var y) v, q')) <- one nctx q
        (w, p') <- unbind bp
        let s' = (x,y) .: sp .++ sq
        guard $ s' `respects` nctx
        return (s', (Tau, Par (subst w v p') q')) -- comm
 <|> do (sp, (Up (Var y) v, p')) <- one nctx p
        (sq, (DnB (Var x), bq)) <- oneb nctx q
        (w, q') <- unbind bq
        let s' = (x,y) .: sp .++ sq
        guard $ s' `respects` nctx
        return (s', (Tau, Par p' (subst w v q'))) -- comm
one nctx (Nu b) = do (x,p) <- unbind b
                     (s,(l,p')) <- one (Nab x : nctx) p
                     return (s, (l, Nu(x.\p')))
one _    _ = empty

oneb :: (Fresh m, Alternative m) => [Quan] -> Pr -> m (EqC,(ActB, Bind NameTm Pr))
oneb nctx (In x p) = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)
          | x == y    = oneb nctx p
          | otherwise = do (s, r) <- oneb nctx p
                           let s' = (x,y) .: s
                           guard $ s' `respects` nctx
                           return (s', r)
oneb nctx (Plus p q) = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q)
   = do { (s,(l,b')) <- oneb nctx p; (x,p') <- unbind b'; return (s,(l, x.\Par p' q)) }
 <|> do { (s,(l,b')) <- oneb nctx q; (x,q') <- unbind b'; return (s,(l, x.\Par p q')) }
oneb nctx (Nu b)
   = do (x,p) <- unbind b
        (s,(l,b')) <- oneb (Nab x : nctx) p
        (y,p') <- unbind b'
        return (s, (l, y.\Nu(x.\p'))) -- restriction
 <|> do (x,p) <- unbind b
        (s,(Up y (Var x'),p')) <- one (Nab x : nctx) p
        guard $ x == x'
        return (s, (UpB y, x.\p')) -- open
oneb _    _ = empty

-- just to remove duplication by simmetry when consing
-- better optimization might be using Set ... but for now just list
infixr 5 .:
(x,y) .: s = case compare x y of  LT -> (x,y):s
                                  EQ -> s
                                  GT -> (y,x):s

infixr 5 .++
(.++) = union

respects :: EqC -> [Quan] -> Bool
respects s nctx = all (\n -> rep partition n == n) nabixs
  where
    nabixs = [n2i x | Nab x <- nctx]
    partition = foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- s] p0
    p0 = fromDisjointSets (fmap Set.singleton [0..maxVal]) :: Partition Int
    i2n i = revns !! i
    n2i x = n2iMap Map.! x
    revns = reverse $ map q2n nctx :: [NameTm]
    n2iMap = Map.fromList $ zip revns [0..maxVal]
    maxVal = length revns - 1 :: Int
{-
Map names to ints in a decreasing manner, that is,
from nctx :: [NameTm] to [n-1,...,0] :: Int.
The numbering is in reverse order since the most recnelty introduced variable
is at the head of nctx and the outermost at the last. Also map the s to
pairs of ints following the same mapping scheme. Then we can apply "join"
repeatedly for each pair of ints to the all-singleton partition, that is,
[[0],[1],...,[n-1]]. After joining, the "rep" value of each nabla variable
must be itself, being the least element of its equivalence class. Otherwise,
the nabla restriction has been violated because it means that there has been
an attempt to unify a nabla varible with another variable introduced before.
-}

-- build substutition from nctx and equanity constraint list
substitute :: Subst Tm b => [Quan] -> EqC -> b -> b
substitute nctx s = foldr (.) id [subst x (Var y) | (x,y)<-s']
  where
    s' = [(i2n i, i2n $ rep partition i) | i<-[0..maxVal]] -- map to min val
    -- nabixs = [n2i x | Nab x <- nctx]
    partition = foldr (.) id [joinElems (n2i x) (n2i y) | (x,y) <- s] p0
    p0 = fromDisjointSets (fmap Set.singleton [0..maxVal]) :: Partition Int
    i2n i = revns !! i
    n2i x = n2iMap Map.! x
    revns = reverse $ map q2n nctx :: [NameTm]
    n2iMap = Map.fromList $ zip revns [0..maxVal]
    maxVal = length revns - 1 :: Int



-- (open) simulation and bisimulation

freshFrom :: (Fresh m) => [NameTm] -> Bind NameTm Pr -> m NameTm
freshFrom xs b = do { mapM_ fresh xs; (y,_) <- unbind b; fresh y }


sim :: [Quan] -> Pr -> Pr -> Bool
sim nctx p q = (and :: [Bool] -> Bool) $
  do (s, r) <- runFreshMT (one nctx p)
     let (lp, p') = substitute nctx s r
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, q') <- L.one (substitute nctx s q) -- follow by late step
       guard $ lp == lq
       return $ sim nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bp' -- to use same new quan var
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, bq') <- L.oneb (substitute nctx s q) -- follow by late step
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       return $ sim nctx' p' q'

bisim :: [Quan] -> Pr -> Pr -> Bool
bisim nctx p q = (and :: [Bool] -> Bool) $
  do (s, r) <- runFreshMT (one nctx p)
     let (lp, p') = substitute nctx s r
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, q') <- L.one (substitute nctx s q) -- follow by late step
       guard $ lp == lq
       return $ bisim nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bp' -- to use same new quan var
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lq, bq') <- L.oneb (substitute nctx s q) -- follow by late step
       (x, p1, q1) <- unbind2' bp' bq'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       return $ bisim nctx' p' q'
  <|>
  do (s, r) <- runFreshMT (one nctx q)
     let (lq, q') = substitute nctx s r
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lp, p') <- L.one (substitute nctx s p) -- follow by late step
       guard $ lp == lq
       return $ bisim nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx q)
     let (lq, bq') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bq' -- to use same new quan var
     return . (or :: [Bool] -> Bool) . runFreshMT $ do
       (lp, bp') <- L.oneb (substitute nctx s p) -- follow by late step
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       return $ bisim nctx' p' q'

data Rose a = Rose a [Rose a] deriving (Eq,Ord,Show)
rhead :: Rose t -> t
rhead (Rose a _) = a
rtail (Rose _ rs) = rs

data StepLog = One [Quan] EqC Act Pr
             | OneB [Quan] EqC ActB (Bind NameTm Pr)
  deriving (Eq,Ord,Show)

getQuan (One qs _ _ _)  = qs
getQuan (OneB qs _ _ _) = qs

returnL x = return . Rose (Left x)
returnR x = return . Rose (Right x)

fromEither :: Either a a -> a
fromEither (Left t)  = t
fromEither (Right t) = t

sim' :: [Quan] -> Pr -> Pr -> [Rose (Either StepLog StepLog)]
sim' nctx p q =
  do (s, r) <- runFreshMT (one nctx p)
     let (lp, p') = substitute nctx s r
     returnL (One nctx s lp p') . runFreshMT $ do
       (lq, q') <- L.one (substitute nctx s q) -- follow by late step
       guard $ lp == lq
       returnR (One nctx s lq q') $ sim' nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bp' -- to use same new quan var
     returnL (OneB nctx s lp bp') . runFreshMT $ do
       (lq, bq') <- L.oneb (substitute nctx s q) -- follow by late step
       (x, p1, q1) <- unbind2' bp' bq'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       returnR (OneB nctx s lq bq') $ sim' nctx' p' q'

bisim' :: [Quan] -> Pr -> Pr -> [Rose (Either StepLog StepLog)]
bisim' nctx p q =
  do (s, r) <- runFreshMT (one nctx p)
     let (lp, p') = substitute nctx s r
     returnL (One nctx s lp p') . runFreshMT $ do
       (lq, q') <- L.one (substitute nctx s q) -- follow by late step
       guard $ lp == lq
       returnR (One nctx s lq q') $ bisim' nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx p)
     let (lp, bp') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bp' -- to use same new quan var
     returnL (OneB nctx s lp bp') . runFreshMT $ do
       (lq, bq') <- L.oneb (substitute nctx s q) -- follow by late step
       (x, p1, q1) <- unbind2' bp' bq'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       returnR (OneB nctx s lq bq') $ bisim' nctx' p' q'
  <|>
  do (s, r) <- runFreshMT (one nctx q)
     let (lq, q') = substitute nctx s r
     returnR (One nctx s lq q') . runFreshMT $ do
       (lp, p') <- L.one (substitute nctx s p) -- follow by late step
       guard $ lp == lq
       returnL (One nctx s lp p') $ bisim' nctx p' q'
  <|>
  do (s, r) <- runFreshMT (oneb nctx q)
     let (lq, bq') = substitute nctx s r
     let x' = runFreshM $ freshFrom (q2n<$>nctx) bq' -- to use same new quan var
     returnR (OneB nctx s lq bq') . runFreshMT $ do
       (lp, bp') <- L.oneb (substitute nctx s p) -- follow by late step
       (x, q1, p1) <- unbind2' bq' bp'
       let (p', q') | x == x'   = (p1, q1) -- to use same new quan var
                    | otherwise = subst x (Var x') (p1, q1)
       let nctx' = case lp of DnB _ -> All x' : nctx
                              UpB _ -> Nab x' : nctx
       guard $ lp == lq
       returnL (OneB nctx s lp bp') $ bisim' nctx' p' q'


roses2df :: [Rose (Either StepLog StepLog)] -> [(Formula,Formula)]
roses2df rs =
  -- base cases
  do (sp, a) <- [(sp, a) | Rose (Left (One _ sp a _)) [] <- rs]
     let formL = preCbase sp a
     let subRs = [sq | Rose (Right (One _ sq a' _)) _ <- rs, a==a']
     if null subRs then return (formL, Box a FF)
       else do { sq <- subRs; return (formL, postCbase sq a) }
  <|>
  do (sq, a) <- [(sq, a) | Rose (Right (One _ sq a _)) [] <- rs]
     let formR = preCbase sq a
     let subLs = [sp | Rose (Left (One _ sp a' _)) _ <- rs, a==a']
     if null subLs then return (Box a FF, formR)
       else do { sp <- subLs; return (postCbase sp a, formR) }
  <|>
  do (sp, a) <- [(sp, a) | Rose (Left (OneB _ sp a _)) [] <- rs]
     let formL = preCbaseB sp a
     let subRs = [sq | Rose (Right (OneB _ sq a' _)) _ <- rs, a==a']
     if null subRs then return (formL, BoxB a $ constbind FF)
       else do { sq <- subRs; return (formL, postCbaseB sq a) }
  <|>
  do (sq, a) <- [(sq, a) | Rose (Right (OneB _ sq a _)) [] <- rs]
     let formR = preCbaseB sq a
     let subLs = [sp | Rose (Left (OneB _ sp a' _)) _ <- rs, a==a']
     if null subLs then return (BoxB a $ constbind FF, formR)
       else do { sp <- subLs; return (postCbaseB sp a, formR) }
  -- inductive cases
  <|>
  do Rose (Left (One _ s a _)) rsR <- rs
     let rss' = [rs' | Rose _ rs' <- rsR]
     (dfsL,dfsR) <- unzip <$> sequence (roses2df <$> rss')
     guard . not . null $ dfsL
     return (preC s a dfsL, postC s a dfsR)
  <|>
  do Rose (Right (One _ s a _)) rsL <- rs
     let rss' = [rs' | Rose _ rs' <- rsL]
     (dfsL,dfsR) <- unzip <$> sequence (roses2df <$> rss')
     guard . not . null $ dfsL
     return (postC s a dfsL, preC s a dfsR)
  --  TODO B inductive cases
  <|>
  do Rose (Left (OneB nctx s a _)) rsR <- rs
     let rss' = [rs' | Rose _ rs' <- rsR]
         x = q2n . head . getQuan . fromEither . rhead . head $ head rss'
     (dfsL,dfsR) <- unzip <$> sequence (roses2df <$> rss')
     guard . not . null $ dfsL
     return (preCB s a x dfsL, postCB s a x dfsR)
  <|>
  do Rose (Right (OneB nctx s a _)) rsL <- rs
     let rss' = [rs' | Rose _ rs' <- rsL]
         x = q2n . head . getQuan . fromEither . rhead . head $ head rss'
     (dfsL,dfsR) <- unzip <$> sequence (roses2df <$> rss')
     guard . not . null $ dfsL
     return (postCB s a x dfsL, preCB s a x dfsR)
  where
    preCbase s a = boxMatch s $ Dia a TT
    postCbase s a = Box a $ diaMatch s
    preCbaseB s a = boxMatch s . DiaB a $ constbind TT
    postCbaseB s a = BoxB a . constbind $ diaMatch s
    preC s a = boxMatch s . Dia a . conj
    postC [] a fs = Box a $ disj fs
    postC s  a fs = Box a $ disj (diaMatch s : fs)
    preCB s a x = boxMatch s . DiaB a . bind x . conj
    postCB [] a x fs = BoxB a . bind x $ disj fs
    postCB s  a x fs = BoxB a . bind x $ disj (diaMatch s : fs)
    constbind =  bind (s2n "_")
    boxMatch [] = id
    boxMatch s  = BoxMatch [(Var x,Var y) | (x,y)<-s]
    diaMatch [] = FF
    diaMatch s  = DiaMatch [(Var x,Var y) | (x,y)<-s] TT
