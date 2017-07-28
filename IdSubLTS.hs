{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}

module IdSubLTS where
import           Control.Applicative
import           Control.Monad
import           PiCalc
import           Unbound.LocallyNameless hiding (Con, empty)
{-# ANN module "HLint: ignore Use mappend" #-}

-- TODO redTm
redPr (Match x y p) | x == y = return p
redPr (Let b)
  = do ((pat,Embed t), p) <- unbind b
       -- TODO well formedness chk e.g. pat should not contain duplicat vars
       case (pat, t) of
         (V x, _) -> return (subst x t p)
         (D "pair" [pat1, pat2], D "pair" [t1, t2])
            -> return $ Let (bind (pat1,embed t1) $ Let (bind (pat2,embed t2) p))
         (D "pair" [_, _], _) -> empty
         (D "enc" [_, _], _) -> empty
         _ -> fail $ "unsupported pattern " ++ show pat
redPr _ = empty

one :: (Fresh m, Alternative m) => Pr -> m (Act, Pr)
one (TauP p)   = return (Tau, p)
one (Plus p q) = one p <|> one q
one (Par p q) =    do  (l, p') <- one p;  return (l, Par p' q)
              <|>  do  (l, q') <- one q;  return (l, Par p q')
              <|>  do  (Up x, pc) <- oneb p;  (Dn x', qa) <- oneb q
                       guard $ x == x';  (,) Tau <$> conabs pc qa
              <|>  do  (Dn x', pa) <- oneb p;  (Up x, qc) <- oneb q
                       guard $ x == x';  (,) Tau <$> abscon pa qc
one (Nu b) = do (x,p) <- unbind b;  (l,p') <- one p
                guard $ x `notElem` (fv l :: [Nm])
                return (l, Nu (x.\p'))
one p          = one =<< redPr p

oneb :: (Fresh m, Alternative m) => Pr -> m (Act, Ag)
oneb (In x p)    = return (Dn x, Abs p)
oneb (Out x y p) = return (Up x, Con y p)
oneb (Plus p q)  = oneb p <|> oneb q
oneb (Par p q)   =     do  (l,pa) <- oneb p;  (,) l <$> parAP pa q
                 <|>   do  (l,qa) <- oneb q;  (,) l <$> parPA p qa
oneb (Nu b)
  =     do  (x,p) <- unbind b;  (l,pa) <- oneb p
            case (l,pa) of
              (Dn _, Abs bp) -> do (y,p') <- unbind bp;
                                   return (l, Abs $ y.\ Nu(x.\p'))
              (Up _, _) -> undefined {-
                | x `notElem` (fv l :: [Nm])
                            ->
                | otherwise ->
                                      Dn _ | x `notElem` (fv l :: [Nm]) -> empty
                                      _    -> return (l, y.\Nu (x.\p'))
                        -}
oneb p           = oneb =<< redPr p

-- oneb' p = do (l,b) <- oneb p; r <- unbind b; return (l,r)


abscon, conabs :: Fresh m => Ag -> Ag -> m Pr
abscon (Abs bp) (Con t q) = do (x,p) <- unbind bp; return $ subst x t p `Par` q
abscon pa (New bq) = do (x,qc) <- unbind bq; Nu . (x.\) <$> abscon pa qc
conabs (Con t p) (Abs bq) = do (x,q) <- unbind bq; return $ p `Par` subst x t q
conabs (New bp) qa = do (x,pc) <- unbind bp; Nu . (x.\) <$> conabs pc qa

parAP :: Fresh m => Ag -> Pr -> m Ag
parAP (Con t p) q = return . Con t $ p `Par` q
parAP (New bp) q  = do (x,pa) <- unbind bp;  New . (x.\) <$> parAP pa q
parAP (Abs bp) q  = do (x,p) <- unbind bp; return . Abs $ x.\ p `Par` q
parPA :: Fresh m => Pr -> Ag -> m Ag
parPA p (Con t q) = return . Con t $ p `Par` q
parPA p (New bq)  = do (x,qa) <- unbind bq;  New . (x.\) <$> parPA p qa
parPA p (Abs bq)  = do (x,q) <- unbind bq; return . Abs $ x.\ p `Par` q
