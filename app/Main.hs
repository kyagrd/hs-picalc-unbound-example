-- {-# LANGUAGE FlexibleContexts          #-}
-- {-# LANGUAGE FlexibleInstances         #-}
-- {-# LANGUAGE MultiParamTypeClasses     #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
-- {-# LANGUAGE ScopedTypeVariables       #-}
-- {-# LANGUAGE TemplateHaskell           #-}
-- {-# LANGUAGE UndecidableInstances      #-}
module Main where

import           LateLTS
import           OpenLTS                 (Quan (..), respects)
import qualified OpenLTS                 as O
import           PiCalc
import           SubstLatt               (someFunc)
import           Unbound.LocallyNameless

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

x, y, z :: NameTm
w = s2n "w"
x = s2n "x"
y = s2n "y"
z = s2n "z"

q1 = TauP q2
q2 = Match (Var x) (Var y) (TauP Null)

p1 = TauP Null `Plus` TauP (TauP Null)
p2 = In (Var x) (bind z $ Out (Var x) (Var z) Null) `Par` Out (Var x) (Var y) Null

axay = reverse [All x, All y]
axny = reverse [All x, Nab y]
nxay = reverse [Nab x, All y]
nxny = reverse [Nab x, Nab y]
axayazaw = reverse $ map All [x,y,z,w]



printLateOneFrom p = do
  putStrLn $ "one step from: " ++ show p
  mapM_ print (runFreshMT (one p) :: [(Act,Pr)])


printOpenOneFrom nctx p = do
  putStrLn $ "one step from: " ++ show (reverse nctx) ++ " "++ show p
  mapM_ print (runFreshMT (O.one nctx p) :: [([(NameTm,NameTm)],(Act,Pr))])

main :: IO ()
main = do
  putStrLn "================================================================"
  putStrLn "== Late LTS"
  putStrLn "================================================================"
  printLateOneFrom p1
  putStrLn "================================================================"
  printLateOneFrom q1
  putStrLn "================================================================"
  printLateOneFrom q2
  putStrLn "================================================================"
  printLateOneFrom p2
  putStrLn "================================================================"
  putStrLn ""
  putStrLn "================================================================"
  putStrLn "== Late LTS"
  putStrLn "================================================================"
  printOpenOneFrom axay p1
  putStrLn "================================================================"
  printOpenOneFrom axay q1
  putStrLn "================================================================"
  printOpenOneFrom axay q2
  putStrLn "================================================================"
  printOpenOneFrom axny q2
  putStrLn "================================================================"
  printOpenOneFrom nxay q2
  putStrLn "================================================================"
  printOpenOneFrom nxny q2
  putStrLn "================================================================"
  printOpenOneFrom axay p2
  putStrLn "================================================================"
  putStrLn ""
  print (runFreshMT dosomething :: [Pr])
  print (runFreshMT dosomething2 :: [Bind NameTm Pr])

dosomething = do
  (s,(l,p')) <- O.one nctx p
  return $ O.substitute nctx s p'
  where
  nctx = axayazaw
  p =
      Match (Var x) (Var w) $ Match (Var z) (Var x) $
      -- Match (Var x) (Var y) $ Match (Var w) (Var z) $
      TauP (Out (Var x) (Var w) Null) `Plus` TauP (Out (Var y) (Var z) Null)

dosomething2 = do
  (s,(l,bp')) <- O.oneb nctx p
  return $ O.substitute nctx s bp'
  where
    nctx = []
    p = Nu$x.\(In (Var x) $y.\TauP Null)
{-
*Main Lib> :t runFreshMT (one p1)
runFreshMT (one p1) :: MonadPlus m => m (Act, Pr)
*Main Lib> runFreshMT (one p1) :: [(Act,Pr)]
[(Tau,Null),(Tau,TauP Null)]
*Main Lib> runFreshMT (one q1) :: [(Act,Pr)]
[(Tau,Match (Var x) (Var y) (TauP Null))]
*Main Lib> runFreshMT (one p2) :: [(Act,Pr)]
[(Up (Var x) (Var y),Par (In (Var x) (bind z(Out (Var x) (Var 0@0) Null))) Null),(Tau,Par (Out (Var x) (Var y) Null) Null)]
-}
