{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
-- {-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module Main where

import qualified IdSubLTS                as IdS 
import           OpenLTS
import           OpenBisim
import           PiCalc
import           SubstLatt               (someFunc)
import           Unbound.LocallyNameless
import           Data.Tree
import           Text.PrettyPrint
import           Text.PrettyPrint.HughesPJClass

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

pp = print . pPrint

instance Pretty Nm where pPrint = text . show
instance Pretty Quan where
  pPrint (All x) = text "All" <+> pPrint x
  pPrint (Nab x) = text "Nab" <+> pPrint x
instance Pretty Tm where pPrint (Var x) = parens $ text "Var" <+> pPrint x
instance Pretty Act where
  pPrint (Up x y) = text "Up" <+> pPrint x <+> pPrint y
  pPrint Tau = text "Tau"
instance Pretty ActB where
  pPrint (UpB x) = text "UpB" <+> pPrint x
  pPrint (DnB x) = text "DnB" <+> pPrint x
instance (Alpha a, Pretty a) => Pretty (Bind Nm a) where
  pPrint b = parens $ pPrint x <> text ".\\" <> pPrint p
           where (x,p) = runFreshM $ unbind b
instance Pretty Pr where
  pPrint Null = text "Null"
  pPrint (TauP p) = parens $ text "TauP" <+> pPrint p
  pPrint (Out x y p) = parens $ text "Out" <+> pPrint x <+> pPrint y <+> pPrint p
  pPrint (In x b) = parens $ text "In" <+> pPrint x <+> pPrint b
  pPrint (Plus p q) = parens $ pPrint p <+> text "`Plus`" <+> pPrint q
  pPrint (Par p q) = parens $ pPrint p <+> text "`Par`" <+> pPrint q
  pPrint (Nu b) = parens $ pPrint b
  pPrint (Match x y p) = parens $ text "Match" <+> pPrint x <+> pPrint y <+> pPrint p
instance Pretty Form where
  pPrint FF = text "FF"
  pPrint TT = text "TT"
  pPrint (Conj fs) = parens $ text "Conj" <> pPrint fs
  pPrint (Disj fs) = parens $ text "Disj" <> pPrint fs
  pPrint (Box a f) = parens $ text "Box" <+> parens (pPrint a) <+> pPrint f
  pPrint (Dia a f) = parens $ text "Dia" <+> parens (pPrint a) <+> pPrint f
  pPrint (BoxB a f) = parens $ text "BoxB" <+> parens (pPrint a) <+> pPrint f
  pPrint (DiaB a f) = parens $ text "DiaB" <+> parens (pPrint a) <+> pPrint f
  pPrint (BoxMatch sigma f) = parens $ text "BoxMatch" <+> pPrint sigma <+> pPrint f
  pPrint (DiaMatch sigma f) = parens $ text "DiaMatch" <+> pPrint sigma <+> pPrint f
instance Pretty StepLog where
  pPrint (One  nctx sigma l p) = parens $ text "One" <+> pPrint nctx <+> pPrint sigma <+> pPrint l <+> pPrint p
  pPrint (OneB nctx sigma l b) = parens $ text "OneB" <+> pPrint nctx <+> pPrint sigma <+> pPrint l <+> pPrint b


x, y, z :: Nm
w = s2n "w"
x = s2n "x"
y = s2n "y"
z = s2n "z"

q1 = taup q2
q2 = (x.= y)(taup o)

p1 = tau .+ taup tau
p2 = inp x(z.\out x z o) .| out x y o
p3 = inp x(z.\out x z o) .| out y x o

axay = reverse [All x, All y]
axny = reverse [All x, Nab y]
nxay = reverse [Nab x, All y]
nxny = reverse [Nab x, Nab y]
axayazaw = reverse $ map All [x,y,z,w]

printLateOneFrom p = do
  putStrLn $ "one step from: " ++ render1line (pPrint p)
  mapM_ pp (runFreshMT (IdS.one p) :: [(Act,Pr)])


printOpenOneFrom nctx p = do
  putStrLn $ "one step from: " ++ show (reverse nctx) ++ " "++ render1line (pPrint p)
  mapM_ pp (runFreshMT (one nctx p) :: [([(Nm,Nm)],(Act,Pr))])

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
  putStrLn "================================================================"
  print $ bisim axay (tau .+ taup tau) (TauP $ (x.= y)tau)
  putStrLn . showForest $ bisim' axay (tau .+ taup tau) (TauP $ (x.= y) tau)
  mapM_ print . forest2df $ bisim' axay (tau .+ taup tau) (taup $ (x.= y) tau)
  putStrLn "================================================================"
  print $ bisim axay (taup $ (x.= y) tau) (tau .+ taup tau)
  putStrLn . showForest $ bisim' axay (taup $ (x.= y) tau) (tau .+ taup tau)
  mapM_ pp . forest2df $ bisim' axay (taup $ (x.= y)tau) (tau .+ taup tau)
  putStrLn "================================================================"
  print $ bisim axay (taup ((x.= y) tau) .+ t_tt) t_tt
  putStrLn . showForest $ bisim' axay (taup ((x.= y) tau) .+ t_tt) t_tt
  mapM_ pp . forest2df $ bisim' axay (taup ((x.= y) tau) .+ t_tt) t_tt
  putStrLn "================================================================"
  putStrLn . showForest $ bisim' axay (tau .+ taup tau) (taup $ (x.= y) tau)
  mapM_ pp . forest2df $ bisim' axay (tau .+ taup tau) (taup $ (x.= y) tau)
  putStrLn "================================================================"
  putStrLn . showForest $ bisim' [All x] (inp x$z.\tau .+ tau) (inp x$z.\tau .+ out z x o)
  mapM_ pp . forest2df $ bisim' [All x] (inp x$z.\tau .+ tau) (inp x$z.\tau .+ out z x o)
  putStrLn "================================================================"
  putStrLn . showForest $ bisim' axayazaw ((z.= w) tau) ((x.= y) tau)
  mapM_ pp . forest2df $ bisim' axayazaw ((z.= w) tau) ((x.= y) tau)
  putStrLn "================================================================"
  print $ bisim axayaaab ppp1 qqq1
  putStrLn . showForest $ bisim' axayaaab ppp1 qqq1
  mapM_ pp . forest2df $ bisim' axayaaab ppp1 qqq1
  putStrLn "================================================================"
  print $ bisim [All a] ppp2 qqq2
  putStrLn . showForest $ bisim' [All a] ppp2 qqq2
  mapM_ pp . forest2df $ bisim' [All a] ppp2 qqq2
  putStrLn "================================================================"
  pp (runFreshMT dosomething2 :: [PrB])
  pp (runFreshMT dosomething3 :: [PrB])
  pp (runFreshMT dosomething4 :: [Pr])
  pp (runFreshMT dosomething5 :: [PrB])
  putStrLn "================================================================"
  print $ bisim axay ((x.= y) (taup tau) .+ tau) (taup tau .+ tau)
  putStrLn . showForest $ bisim' axay ((x.= y) (taup tau) .+ tau) (taup tau .+ tau)
  mapM_ pp . forest2df $ bisim' axay ((x.= y) (taup tau) .+ tau) (taup tau .+ tau)
  putStrLn "================================================================"
  print $ bisim [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))
  putStrLn . showForest $ bisim' [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))
  mapM_ pp . forest2df $ bisim' [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))

showForest = drawForest . map toTreeString
showTree = drawTree . toTreeString

render1line = renderStyle style{mode=OneLineMode}

toTreeString = foldTree (\log ts -> Node (render1line . pPrint $ log) ts)

foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f = go where go (Node x ts) = f x (map go ts)

axayaaab = map All [x,y,a,b]
a = s2n "a"
b = s2n "b"

ppp1 = taup(out a a o .+out b b o) .+ (x.= y) (taup $ out a a o)
qqq1 = taup(out a a o .+out b b o) .+ taup (out a a o)

ppp2 = nu$x.\out a x (inp a $y.\tau)
qqq2 = nu$x.\out a x (inp a $y.\(x.= y) tau)

t_tt = tau .+ taup tau

dosomething = do
  (s,(l,p')) <- one nctx p
  return $ subs nctx s p'
  where
  nctx = axayazaw
  p =
      (x.= w) . (z.= x) $
      -- (x.= y) . (w.= z) $
      taup (out x w o) .+ taup (out y z o)

dosomething2 = do
  (s,(l,bp')) <- oneb nctx p
  return $ subs nctx s bp'
  where
    nctx = []
    p = Nu$x.\(inp x$y.\taup o)

dosomething3 = do
  (s,(l,bp')) <- oneb nctx p
  return $ subs nctx s bp'
  where
    nctx = [All a]
    p = Nu$x.\(out a x o)

dosomething4 = do
  (s,(l,p')) <- one nctx p
  return $ subs nctx s p'
  where
    nctx = [All a]
    p = Nu$x.\(out a x o)

dosomething5 = do
  (s,(l,bp')) <- oneb nctx p
  return $ subs nctx s bp'
  where
    nctx = [All a]
    p = Nu$x.\(out x a o)


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
