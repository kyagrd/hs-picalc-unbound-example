{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module IdSubLTS where
import           Control.Applicative
import           Control.Applicative.Alternative
import           Control.Monad
import qualified Data.Set                        as Set
import           PiCalc
import           Unbound.LocallyNameless         hiding (empty)

type NmSet = Set.Set Nm

one :: (Fresh m, Alternative m) => NmSet -> Pr -> m (Act, Pr)
one _  (Out x y p)    = return (Up x y, p)
one ns (In x b)       = do (z,p) <- unbind b
                           asum [ return (Dn x (Var y), subst z (Var y) p)
                                        | y <- Set.toList(Set.insert z ns) ]
one _  (TauP p)       = return (Tau, p)
one ns (Match x y p)  | x == y = one ns p
one ns (Diff (Var x) (Var y) p)
  | (Set.member x ns || Set.member y ns) && x /= y   = one ns p
one ns (Plus p q) = one ns p <|> one ns q
one ns (Par p q)
  =    do  (l, p') <- one ns p;  return (l, Par p' q)
  <|>  do  (l, q') <- one ns q;  return (l, Par p q')
  <|>  do  (UpB x, bp) <- oneb ns p
           (y, p') <- unbind bp
           (Dn x' (Var z), q') <- one ns q
           guard $ x == x' && not(Set.member z ns)
           return (Tau, Nu(y.\Par p' (subst z (Var y) q'))) -- close
  <|>  do  (UpB x, bq) <- oneb ns q
           (y, q') <- unbind bq
           (Dn x' (Var z), p') <- one ns p
           guard $ x == x' && not(Set.member z ns)
           return (Tau, Nu(y.\Par (subst z (Var y) p') q')) -- close
  <|>  do  (Up x y, p') <- one ns p;  (Dn x' y', q') <- one ns q
           guard $ x == x' && y == y'
           return (Tau, Par p' q')  -- interaction
  <|>  do  (Dn x' y', p') <- one ns p;  (Up x y, q') <- one ns q
           guard $ x == x' && y == y'
           return (Tau, Par p' q')  -- interaction
one ns (Nu b)  = do  (x,p) <- unbind b
                     (l,p') <- one (Set.insert x ns) p
                     case l of  Up (Var x') (Var y)  | x == x'  -> empty
                                                     | x == y   -> empty
                                _                    -> return (l, Nu (x.\p'))
one _ _       = empty

oneb :: (Fresh m, Alternative m) => NmSet -> Pr -> m (ActB, PrB)
oneb ns (Match x y p) | x == y = oneb ns p
oneb ns (Diff (Var x) (Var y) p)
  | (Set.member x ns || Set.member y ns) && x /= y   = oneb ns p
oneb ns (Plus p q)  = oneb ns p <|> oneb ns q
oneb ns (Par p q)   =     do  (l,(x,p')) <- oneb' ns p;  return (l, x.\Par p' q)
                    <|>   do  (l,(x,q')) <- oneb' ns q;  return (l, x.\Par p q')
oneb ns (Nu b)      =     do  (x,p) <- unbind b
                              (l,(y,p')) <- oneb' (Set.insert x ns) p
                              case l of  UpB (Var x')    | x == x' -> empty
                                         _              -> return (l, y.\Nu (x.\p'))
                    <|>   do  (x,p) <- unbind b
                              (Up y (Var x'),p') <- one ns p
                              guard $ x == x' && Var x /= y
                              return (UpB y, x.\p')  -- open
oneb _ _           = empty

oneb' ns p = do (l,b) <- oneb ns p; r <- unbind b; return (l,r)




{- -- below is not a valid qusi-open bisimulation definition  just an exercise

freshFrom :: Fresh m => [Nm] -> PrB -> m Nm
freshFrom xs b = do { mapM_ fresh xs; fst <$> unbind b }

sim ns p q = and $ sim2_ ns p q

sim2_ :: NmSet -> Pr -> Pr -> [Bool]
sim2_ ns p q =
       do  (lp, p') <- runFreshMT (one ns p)
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, q') <- one ns q
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ sim2_ ns p' q'
  <|>  do  (lp, bp') <- runFreshMT (oneb ns p)
           let x' = runFreshM $ freshFrom (fv $ Set.toList ns) bp'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, bq') <- oneb ns q
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ sim2_ ns' p' q'


bisim ns p q = and $ bisim2_ ns p q

bisim2_ :: NmSet -> Pr -> Pr -> [Bool]
bisim2_ ns p q =
       do  (lp, p') <- runFreshMT (one ns p)
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, q') <- one ns q
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ bisim2_ ns p' q'
  <|>  do  (lp, bp') <- runFreshMT (oneb ns p)
           let x' = runFreshM $ freshFrom (fv $ Set.toList ns) bp'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lq, bq') <- oneb ns q
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ bisim2_ ns' p' q'
  <|>  do  (lq, q') <- runFreshMT (one ns q)
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lp, p') <- one ns p
             guard $ lp == lq
             return . (and :: [Bool] -> Bool) $ bisim2_ ns p' q'
  <|>  do  (lq, bq') <- runFreshMT (oneb ns q)
           let x' = runFreshM $ freshFrom (fv $ Set.toList ns) bq'
           return . (or :: [Bool] -> Bool) . runFreshMT $ do
             (lp, bp') <- oneb ns p
             guard $ lp == lq
             (x, q1, p1) <- unbind2' bq' bp'
             let (p', q')  | x == x'    = (p1, q1)
                           | otherwise  = subst x (Var x') (p1, q1)
             let ns' = Set.insert x' ns
             return . (and :: [Bool] -> Bool) $ bisim2_ ns' p' q'
-}
