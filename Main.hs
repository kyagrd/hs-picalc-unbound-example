-- vim: sw=2: ts=2: expandtab: ai:
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
-- {-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}
module Main where

import qualified Data.Set                       as Set
import           Data.Tree
import qualified IdSubLTS                       as IdS
import           OpenBisim
import           OpenLTS
import           PiCalc
import           SubstLatt                      (someFunc)
import           Text.PrettyPrint
import           Text.PrettyPrint.HughesPJClass
import           Unbound.LocallyNameless

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

main = print "hello, world"

appPrec :: Rational
appPrec = 10

pp = print . pPrint

instance Pretty Nm where pPrint = text . show

instance Pretty Quan where
  pPrintPrec l r (All x) = maybeParens (r > appPrec) $ text "All" <+> ppp x
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Nab x) = maybeParens (r > appPrec) $ text "Nab" <+> ppp x
    where ppp = pPrintPrec l (appPrec+1)

instance Pretty Tm where
  pPrintPrec l r (Var x) = maybeParens (r > appPrec) $ text "Var" <+> ppp x
    where ppp = pPrintPrec l (appPrec+1)
instance Pretty Act where
  pPrintPrec l r (Up x y) = maybeParens (r > appPrec) $ text "Up" <+> ppp x <+> ppp y
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r Tau = text "Tau"
instance Pretty ActB where
  pPrintPrec l r (UpB x) = maybeParens (r > appPrec) $ text "UpB" <+> ppp x
    where ppp = pPrintPrec l (appPrec+1)
--  pPrintPrec l r (DnB x) = maybeParens (r > appPrec) $ text "DnB" <+> ppp x
--    where ppp = pPrintPrec l (appPrec+1)
instance (Alpha a, Pretty a) => Pretty (Bind Nm a) where
  pPrintPrec l r b = maybeParens (r > appPrec) $ ppp x <> text ".\\" <> ppp p
    where ppp = pPrintPrec l (appPrec+1); (x,p) = runFreshM $ unbind b
instance Pretty Pr where
  pPrintPrec _ _ Null = text "Null"
  pPrintPrec l r (TauP p) = maybeParens (r > appPrec) $
            text "TauP" <+> ppp p
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Out x y p) = maybeParens (r > appPrec) $
            text "Out" <+> ppp x <+> ppp y <+> ppp p
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (In x b) = maybeParens (r > appPrec) $
            text "In" <+> ppp x <+> ppp b
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Plus p q) = maybeParens (r > appPrec) $
            ppp p <+> text "`Plus`" <+> ppp q
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Par p q) = maybeParens (r > appPrec) $
            ppp p <+> text "`Par`" <+> ppp q
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Nu b) = maybeParens (r > appPrec) $
            text "Nu" <> ppp b
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Match x y p) = maybeParens (r > appPrec) $
            text "Match" <+> ppp x <+> ppp y <+> ppp p
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Diff x y p) = maybeParens (r > appPrec) $
            text "Diff" <+> ppp x <+> ppp y <+> ppp p
    where ppp = pPrintPrec l (appPrec+1)
{-
instance Pretty Form where
  pPrintPrec _ _ FF = text "FF"
  pPrintPrec _ _ TT = text "TT"
  pPrintPrec l r (Conj fs) = maybeParens (r > appPrec) $
            text "Conj" <> ppp fs
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Disj fs) = maybeParens (r > appPrec) $
            text "Disj" <> ppp fs
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Box a f) = maybeParens (r > appPrec) $
            text "Box" <+> ppp a <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (Dia a f) = maybeParens (r > appPrec) $
             text "Dia" <+> ppp a <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (BoxB a f) = maybeParens (r > appPrec) $
            text "BoxB" <+> ppp a <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (DiaB a f) = maybeParens (r > appPrec) $
            text "DiaB" <+> ppp a <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (BoxMatch sigma f) = maybeParens (r > appPrec) $
            text "BoxMatch" <+> ppp sigma <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (DiaMatch sigma f) = maybeParens (r > appPrec) $
            text "DiaMatch" <+> ppp sigma <+> ppp f
    where ppp = pPrintPrec l (appPrec+1)
-}

instance Pretty StepLog where
  pPrintPrec l r (One  nctx ns sigma a p) = maybeParens (r > appPrec) $
            text "One" <+> ppp nctx <+> ppp(Set.toList ns) <+> ppp sigma <+> ppp a <+> ppp p
    where ppp = pPrintPrec l (appPrec+1)
  pPrintPrec l r (OneB nctx ns sigma a b) = maybeParens (r > appPrec) $
            text "OneB" <+> ppp nctx <+> ppp(Set.toList ns) <+> ppp sigma <+> ppp a <+> ppp b
    where ppp = pPrintPrec l (appPrec+1)


x, y, z :: Nm
w = s2n "w"
x = s2n "x"
y = s2n "y"
z = s2n "z"

q1 = taup q2
q2 = (x.= y)(taup o)
q3 = (x./= y)(taup o)

p1 = tau .+ taup tau
p2 = inp x(z.\out x z o) .| out x y o
p3 = inp x(z.\out x z o) .| out y x o

-- good that end of p3 example works
-- TODO confirm this:
{-
> OpenBisim.bisim2 (toCtx' [All a]) Set.empty (nu$z.\(inp a$x.\(inp a$y.\(x./=y)((x.=z)tau .+ (x./=z)tau)))) (nu$z.\(inp a$x.\(inp a$y.\(x./=y)((z.=y)tau .+ (z./=y)tau))))
True


> OpenBisim.bisim2 (toCtx' [All a]) Set.empty (nu$z.\out a z (inp a$x.\(inp a$y.\(x./=y)((x.=z)tau .+ (x./=z)tau)))) (nu$z.\out a z (inp a$x.\(inp a$y.\(x./=y)((z.=y)tau .+ (z./=y)tau))))
-}

a = s2n "a" :: Nm
k = s2n "k" :: Nm
pp1 = nu$k.\ out a k ((inp a$x.\o).+(inp a$x.\tau))
pp2 = nu$k.\ out a k ((inp a$x.\o).+(inp a$x.\tau).+(inp a$x.\(x.=k)tau))


pp1' = nu$k.\ {- out a k -} ((inp a$x.\o).+(inp a$x.\tau))
pp2' = nu$k.\ {- out a k -} ((inp a$x.\o).+(inp a$x.\tau).+(inp a$x.\(x.=k)tau))

qq1 = nu$k.\ {- out a k -} o
qq2 = nu$k.\ {- out a k -} ((a.=k)tau)


qqq1 = nu$k.\ out a k o
qqq2 = nu$k.\ out a k ((a.=k)tau)


qqqq0 = nu$k.\ out a k (inp a$x.\ o)
qqqq1 = nu$k.\ out a k (inp a$x.\ tau)
qqqq2 = nu$k.\ out a k (inp a$x.\ (x.=k)tau)
qqqq3 = nu$k.\ out a k (inp a$x.\ (x./=k)tau)
qqqq4 = nu$k.\ out a k (inp a$x.\ (x.=k)tau .+ (x./=k)tau)


qqqq0' = nu$k.\ {- out a k -} (inp a$x.\ o)
qqqq1' = nu$k.\ {- out a k -} (inp a$x.\ tau)
qqqq2' = nu$k.\ {- out a k -} (inp a$x.\ (x.=k)tau)
qqqq3' = nu$k.\ {- out a k -} (inp a$x.\ (x./=k)tau)
qqqq4' = nu$k.\ {- out a k -} (inp a$x.\ (x.=k)tau .+ (x./=k)tau)

rrr1 = (x./=y) $ taup $ ((x.=z)tau.+(x./=z)tau) .+ ((y.=z)tau.+(y./=z)tau)
rrr2 = (x./=y) $ taup $ tau

rr1 = (x./=y) tau
rr2 = o

rrrr1 = (x./=y) $ taup $ (x.=z)tau.+(x./=z)tau
rrrr2 = (x./=y) $ taup $ (y.=z)tau.+(y./=z)tau


{-
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
  putStrLn "========================================u========================"
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
  print $ bisim axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
  putStrLn . showForest $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
  mapM_ pp . forest2df $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
  putStrLn "================================================================"
  print $ bisim [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))
  putStrLn . showForest $ bisim' [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))
  mapM_ pp . forest2df $ bisim' [All a] (Nu$b.\out a b (inp a $x.\(x.= b) (out x x o))) (Nu$b.\out a b (inp a $x.\out x x o))
-}
showForest = drawForest . map toTreeString
showTree = drawTree . toTreeString

render1line = renderStyle style{mode=OneLineMode}

toTreeString = foldTree (\log ts -> Node (render1line . pPrint $ log) ts)

foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f = go where go (Node x ts) = f x (map go ts)
{-
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
    p = Nu$x.\ out a x o

dosomething4 = do
  (s,(l,p')) <- one nctx p
  return $ subs nctx s p'
  where
    nctx = [All a]
    p = Nu$x.\ out a x o

dosomething5 = do
  (s,(l,bp')) <- oneb nctx p
  return $ subs nctx s bp'
  where
    nctx = [All a]
    p = Nu$x.\ out x a o


nm2bdw :: Fresh m => Nm -> m String
nm2bdw x = return $ show x

tm2bdw :: Fresh m => Tm -> m String
tm2bdw (Var x) = nm2bdw x

act2bdw :: Fresh m => Act -> m String
act2bdw Tau      = return "tau"
act2bdw (Up x y) = (\x y -> "(up "++x++" "++y++")") <$> tm2bdw x <*> tm2bdw y

actb2bdw :: Fresh m => ActB -> m String
actb2bdw (UpB x) = (\x -> "(up "++x++")") <$> (tm2bdw x)
actb2bdw (DnB x) = (\x -> "(dn "++x++")") <$> (tm2bdw x)

pr2bdw :: Fresh m => Pr -> m String
pr2bdw Null = return "z"
pr2bdw (TauP p) = (\p->"(taup "++p++")") <$> pr2bdw p
pr2bdw (Out x y p) = (\x y p->"(out "++x++" "++y++" "++p++")")
                        <$> tm2bdw x <*> tm2bdw y <*> pr2bdw p
pr2bdw (In x b) = do (w,p) <- unbind b
                     (\x w p->"(in "++x++" "++w++"\\"++p++")")
                        <$> tm2bdw x <*> nm2bdw w <*> pr2bdw p
pr2bdw (Match x y p) = (\x y p->"(match "++x++" "++y++" "++p++")")
                        <$> tm2bdw x <*> tm2bdw y <*> pr2bdw p
pr2bdw (Plus p q) = (\p q->"(plus "++p++" "++q++")") <$> pr2bdw p <*> pr2bdw q
pr2bdw (Par p q) = (\p q->"(par "++p++" "++q++")") <$> pr2bdw p <*> pr2bdw q
pr2bdw (Nu b) = do (w,p) <- unbind b
                   (\w p->"(nu "++w++"\\"++p++")") <$> nm2bdw w <*> pr2bdw p

form2bdw :: Fresh m => Form -> m String
form2bdw FF = return "ff"
form2bdw TT = return "tt"
form2bdw (Conj []) = form2bdw TT
form2bdw (Conj [f]) = form2bdw f
form2bdw (Conj fs) = foldr1 (\x y -> "(conj "++x++" "++y++")") <$> mapM form2bdw fs
form2bdw (Disj []) = form2bdw FF
form2bdw (Disj [f]) = form2bdw f
form2bdw (Disj fs) = foldr1 (\x y -> "(disj "++x++" "++y++")") <$> mapM form2bdw fs
form2bdw (Dia a f) = (\a f -> "(diaAct "++a++" "++f++")") <$> act2bdw a <*> form2bdw f
form2bdw (Box a f) = (\a f -> "(boxAct "++a++" "++f++")") <$> act2bdw a <*> form2bdw f
form2bdw (DiaB (UpB x) b) = do (w,f) <- unbind b
                               (\x w f->"(diaOut "++x++" "++w++"\\"++f++")")
                                 <$> tm2bdw x <*> nm2bdw w <*> form2bdw f
form2bdw (DiaB (DnB x) b) = do (w,f) <- unbind b
                               (\x w f->"(diaInL "++x++" "++w++"\\"++f++")")
                                 <$> tm2bdw x <*> nm2bdw w <*> form2bdw f
form2bdw (BoxB (UpB x) b) = do (w,f) <- unbind b
                               (\x w f->"(boxOut "++x++" "++w++"\\"++f++")")
                                 <$> tm2bdw x <*> nm2bdw w <*> form2bdw f
form2bdw (BoxB (DnB x) b) = do (w,f) <- unbind b
                               (\x w f->"(boxIn "++x++" "++w++"\\"++f++")")
                                 <$> tm2bdw x <*> nm2bdw w <*> form2bdw f
form2bdw f@(DiaMatch [] _) = error (show f)
form2bdw (DiaMatch cs f) =
  foldr (\(x,y) f -> "(diaMatch "++x++" "++y++" "++f++")")
    <$> form2bdw f <*> sequence [(,)<$>tm2bdw x<*>tm2bdw y|(x,y)<-cs]
form2bdw f@(BoxMatch [] _) = error (show f)
form2bdw (BoxMatch cs f) =
  foldr (\(x,y) f -> "(boxMatch "++x++" "++y++" "++f++")")
    <$> form2bdw f <*> sequence [(,)<$>tm2bdw x<*>tm2bdw y|(x,y)<-cs]

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

-}
