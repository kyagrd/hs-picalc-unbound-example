{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
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
import           Unbound.LocallyNameless          hiding (empty, fresh, join)
import qualified Unbound.LocallyNameless          as LN

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}



type NamePr = Name Pr

data Pr
  = Var NamePr
  | In NamePr (Bind NamePr Pr)
  | Out NamePr NamePr (Bind NamePr Pr)
  | Nu (Bind NamePr Pr)
  | Bang Pr
  | Match NamePr NamePr Pr
  | Null
  deriving Show

instance Eq Pr where (==) = aeq

$(derive [''Pr])

instance Alpha Pr

instance Subst Pr Pr where
  isvar (Var v) = Just (SubstName v)
  isvar _       = Nothing

---- if you are to define unification kind of thing with Hashmap
-- instance Hashable NamePr where
--   hashWithSalt s n = hashWithSalt s (name2String n, name2Integer n)



main :: IO ()
main = someFunc
