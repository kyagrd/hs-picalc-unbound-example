-- preamble of this |OpenLTS| module is on Figure~\ref{fig:figureOpenLTS}

one :: (Fresh m, Alternative m) => Ctx -> Pr -> m (EqC,(Act,Pr))
one nctx  (Out x y p)   = return ([], (Up x y, p))
one nctx  (TauP p)      = return ([], (Tau, p))
one nctx  (Match (Var x) (Var y) p)  | x == y                   = one nctx p
                                     | [(x,y)] `respects` nctx  =
                                           do  (sigma, r) <- one nctx p
                                               let sigma' = (x,y) .: sigma
                                               guard $ sigma' `respects` nctx
                                               return (sigma', r)
one nctx  (Plus p q) = one nctx p <|> one nctx q
one nctx  (Par p q)
  =    do  (sigma,(l,p')) <- one nctx p; {-"~$~$"-} return (sigma,(l,Par p' q))
  <|>  do  (sigma,(l,q')) <- one nctx q; {-"~$~$"-} return (sigma,(l,Par p q'))
  <|>  do  (sigma_p,(lp,bp)) <- oneb nctx p; {-"~$~$"-} (sigma_q,(lq,bq)) <- oneb nctx q
           case (lp, lq) of            {-"\quad\!\!"-} -- close
             (DnB(Var x),UpB(Var x'))  -> do  (y, q', p') <-  unbind2' bq bp
                                              let sigma' = (x,x') .: sigma_p .++ sigma_q
                                              guard $ sigma' `respects` nctx
                                              return (sigma', (Tau, Nu(y.\Par p' q')))
             (UpB(Var x'),DnB(Var x))  ->  {-"\ldots"-} -- omitted (close)
             _                         -> empty
  <|>  do  (sigma_p, (Up (Var x) v, p')) <- one nctx p
           (sigma_q, (DnB (Var x'), bq)) <- oneb nctx q; {-""-} (y, q') <- unbind bq
           let sigma' = (x,x') .: sigma_p .++ sigma_q
           guard $ sigma' `respects` nctx
           return (sigma', (Tau, Par p' (subst y v q'))) -- interaction
  <|>  {-"\ldots"-} -- do block symmetric to above omitted (interaction)
one nctx (Nu b) = do  (x,p) <- unbind b;              let nctx' = Nab x : nctx
                      (sigma,(l,p')) <- one nctx' p;  let sigmaSubs = subs nctx' sigma
                      case l of  Up (Var x') (Var y)  | x == sigmaSubs x'  -> empty
                                                      | x == sigmaSubs y   -> empty
                                 _                    -> return (sigma, (l, Nu(x.\p')))
one _    _      = empty

oneb :: (Fresh m, Alternative m) => Ctx -> Pr -> m (EqC,(ActB, PrB))
oneb nctx (In x p) = return ([], (DnB x, p))
oneb nctx (Match (Var x) (Var y) p)  | x == y                   = oneb nctx p
                                     | [(x,y)] `respects` nctx  = {-"\ldots"-} -- omitted
oneb nctx (Plus p q) = oneb nctx p <|> oneb nctx q
oneb nctx (Par p q) = {-"\ldots"-} -- omitted 
oneb nctx (Nu b)  =    do  (x,p) <- unbind b;                    let nctx' = Nab x : nctx
                           (sigma,(l,(y,p'))) <- oneb' nctx' p;  let sigmaSubs = subs nctx' sigma
                           case l of  UpB (Var x')  | x == sigmaSubs x' -> empty
                                      DnB (Var x')  | x == sigmaSubs x' -> empty
                                      _             -> return (sigma, (l, y.\Nu (x.\p')))
                  <|>  do  (x,p) <- unbind b;                          let nctx' = Nab x : nctx
                           (sigma,(Up y (Var x'),p')) <- one nctx' p;  let sigmaSubs = subs nctx' sigma
                           guard $ x == sigmaSubs x' && Var x /= sigmaSubs y
                           return (sigma, (UpB y, x.\p')) -- open
oneb _    _ = empty

oneb' nctx p = do (sigma,(l,b)) <- oneb nctx p; r <- unbind b; return (sigma,(l,r))
