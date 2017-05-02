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

q1 = taup q2
q2 = match x y (taup o)

p1 = tau .+ taup tau
p2 = inp x(z.\out x z o) .| out x y o
p3 = inp x(z.\out x z o) .| out y x o

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
  printLateOneFrom p3
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
  printOpenOneFrom axay p3
  putStrLn "================================================================"
  putStrLn ""
  print (runFreshMT dosomething :: [Pr])
  print (runFreshMT dosomething2 :: [Bind NameTm Pr])
  print $ O.bisim axay (tau .+ taup tau) (TauP $ match x y tau)
  mapM_ print $ O.bisim' axay (tau .+ taup tau) (TauP $ match x y tau)
  mapM_ print . O.roses2df $ O.bisim' axay (tau .+ taup tau) (taup $ match x y tau)
  print $ O.bisim axay (taup $ match x y tau) (tau .+ taup tau)
  mapM_ print $ O.bisim' axay (taup $ match x y tau) (tau .+ taup tau)
  mapM_ print . O.roses2df $ O.bisim' axay (taup $ match x y tau) (tau .+ taup tau)
  mapM_ print $ O.roses2df $ O.bisim' [All x] (inp x$z.\tau .+ tau) (inp x$z.\tau .+ out z x o)
  mapM_ print $ O.roses2df $ O.bisim' axayazaw (match z w tau) (match x y tau)



dosomething = do
  (s,(l,p')) <- O.one nctx p
  return $ O.substitute nctx s p'
  where
  nctx = axayazaw
  p =
      match x w . match z x $
      -- match x y . match w z $
      taup (out x w o) .+ taup (out y z o)

dosomething2 = do
  (s,(l,bp')) <- O.oneb nctx p
  return $ O.substitute nctx s bp'
  where
    nctx = []
    p = Nu$x.\(inp x$y.\taup o)



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
