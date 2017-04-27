{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
-- {-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module Main where

import           Lib

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
-- import           Data.Hashable
-- import qualified Data.HashMap.Strict              as Map
import           Data.Maybe
-- import           Unbound.LocallyNameless          hiding (empty, fresh, join)
-- import qualified Unbound.LocallyNameless          as LN
import           Unbound.LocallyNameless          hiding (empty)

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

x, y, z :: NameTm
x = s2n "x"
y = s2n "y"
z = s2n "z"

p1 = TauP Null `Plus` TauP (TauP Null)
q1 = TauP (Match (Var x) (Var y) (TauP Null))


p2 = In (Var x) (bind z $ Out (Var x) (Var z) Null) `Par` Out (Var x) (Var y) Null

main :: IO ()
main = do
  putStrLn $ "one step from: " ++ show p1
  mapM_ print (runFreshMT (one p1) :: [(Act,Pr)])
  putStrLn "================================================================"
  putStrLn $ "one step from: " ++ show q1
  mapM_ print (runFreshMT (one q1) :: [(Act,Pr)])
  putStrLn "================================================================"
  putStrLn $ "one step from: " ++ show p2
  mapM_ print (runFreshMT (one p2) :: [(Act,Pr)])
  putStrLn "================================================================"
{-
*Main Lib> :t runFreshMT (one p1)
runFreshMT (one p1) :: MonadPlus m => m (Act, Pr)
*Main Lib> runFreshMT (one p1) :: [(Act,Pr)]
[(Tau,Null),(Tau,TauP Null)]
*Main Lib> runFreshMT (one q1) :: [(Act,Pr)]
[(Tau,Match (Var x) (Var y) (TauP Null))]
-}
