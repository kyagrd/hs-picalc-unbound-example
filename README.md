# hs-picalc-unbound-example

This program implements quasi-open bisimiulation of the pi-calculus processes with mismatch and automatic generation of their disginguishing formulae in an intuitionistic varient of the modal logic FM. Make sure that you have switch to `quasi` branch of the repositroy because it is not the main branch.

## To build the project

Install [`stack`](https://www.haskellstack.org/), which is a toolset for Haskell
including a sandboxing build system. It can be installed
on debian by ``sudo apt-get install stack`` and
on ubuntu by ``sudo apt-get install haskell-stack``.
After installing stack, make sure that your ``PATH`` environment variable
includes ``$HOME/.local/bin`` where ``$HOME`` is the path to your home directory.
To make sure that everything is up to date and also install a basic utility:
```
stack upgrade
stack install stack-run
```

Then, run the following inside this directroy.
```
stack setup
stack build
```

The ``stack setup`` above only needs to be run once.
After that ``stack build`` is enogh to build after editing the source code.

When the build is successful you can either ``stack run`` to execute the program
or ``stack repl`` to load the program into an interactive enivronment (ghci).

<!-- TODO below are main brach open bisim description. TODO show some run quasi test cases

## Running the motivating example in the paper with `ghci`

```
kyagrd@kya14g:~/bitbkt/atiu-ntu/modal-logic/Haskell17$ stack ghci
hs-picalc-unbound-example-0.1.0.0: build
Preprocessing executable 'hs-picalc-unbound-example-exe' for
hs-picalc-unbound-example-0.1.0.0...
...
...
...
Ok, modules loaded: IdSubLTS, Main, OpenBisim, OpenLTS, PiCalc, SubstLatt.
Loaded GHCi configuration from /tmp/ghci27148/ghci-script
*Main IdSubLTS OpenBisim OpenLTS PiCalc SubstLatt> :l Main
[1 of 6] Compiling SubstLatt        ( /home/kyagrd/bitbkt/atiu-ntu/modal-logic/Haskell17/SubstLatt.hs, interpreted )
[2 of 6] Compiling PiCalc           ( /home/kyagrd/bitbkt/atiu-ntu/modal-logic/Haskell17/PiCalc.lhs, interpreted )
[3 of 6] Compiling OpenLTS          ( /home/kyagrd/bitbkt/atiu-ntu/modal-logic/Haskell17/OpenLTS.lhs, interpreted )
[4 of 6] Compiling IdSubLTS         ( /home/kyagrd/bitbkt/atiu-ntu/modal-logic/Haskell17/IdSubLTS.lhs, interpreted )
[5 of 6] Compiling OpenBisim        ( /home/kyagrd/bitbkt/atiu-ntu/modal-logic/Haskell17/OpenBisim.lhs, interpreted )
[6 of 6] Compiling Main             ( Main.hs, interpreted )
Ok, modules loaded: IdSubLTS, Main, OpenBisim, OpenLTS, PiCalc, SubstLatt.
*Main> axay
[All y,All x]
*Main> bisim axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
False
*Main> print $ bisim axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
False
*Main> putStrLn . showForest $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
Left (One [All y, All x] [] Tau (TauP Null))
|
`- Right (One [All y, All x] [] Tau Null)
   |
   `- Left (One [All y, All x] [] Tau Null)

Left (One [All y, All x] [] Tau Null)
|
`- Right (One [All y, All x] [] Tau Null)

Right (One [All y, All x] [(x, y)] Tau (TauP Null))
|
+- Left (One [All y, All x] [(x, y)] Tau (TauP Null))
|  |
|  +- Left (One [All y, All x] [] Tau Null)
|  |  |
|  |  `- Right (One [All y, All x] [] Tau Null)
|  |
|  `- Right (One [All y, All x] [] Tau Null)
|     |
|     `- Left (One [All y, All x] [] Tau Null)
|
`- Left (One [All y, All x] [(x, y)] Tau Null)
   |
   `- Right (One [All y, All x] [] Tau Null)

Right (One [All y, All x] [] Tau Null)
|
+- Left (One [All y, All x] [] Tau (TauP Null))
|  |
|  `- Left (One [All y, All x] [] Tau Null)
|
`- Left (One [All y, All x] [] Tau Null)


*Main> mapM_ pp . forest2df $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
(Dia Tau (Dia Tau TT),
 Box Tau (Disj[DiaMatch [(Var x, Var y)] TT, Box Tau FF]))
```

## Converting to Bedwyr syntax definition for satisfaction check
The distinguishing formulae above can be converted into Bedwyr syntax definition
to check whether each process satisfies each formula as follows:
```
*Main> let f1 = fst . head . forest2df $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
*Main> let f2 = snd . head . forest2df $ bisim' axay (taup tau .+ tau) ((x.= y) (taup tau) .+ tau)
*Main> let bp1 = bind (quan2nm<$>axay :: [Nm]) (taup tau .+ tau)
*Main> let bf1 = bind (quan2nm<$>axay :: [Nm]) f1
*Main> let bp2 = bind (quan2nm<$>axay :: [Nm]) ((x.= y) (taup tau) .+ tau)
*Main> let bf2 = bind (quan2nm<$>axay :: [Nm]) f2
*Main> putStrLn . runFreshM $ do (xs,p,f)<-unbind2' bp2 bf2; proc<-pr2bdw p; form<-form2bdw f; return $ "forall "++concat(Data.List.intersperse " " $ map show xs)++", sat "++proc++" "++form++"."
forall y1 x, sat (plus (match x y1 (taup (taup z))) (taup z)) (boxAct tau (disj (diaMatch x  y1 tt) (boxAct tau ff))).
*Main> putStrLn . runFreshM $ do (xs,p,f)<-unbind2' bp1 bf1; proc<-pr2bdw p; form<-form2bdw f; return $ "forall "++concat(Data.List.intersperse " " $ map show xs)++", sat "++proc++" "++form++"."
forall y1 x, sat (plus (taup (taup z)) (taup z)) (diaAct tau (diaAct tau tt)).
*Main> putStrLn . runFreshM $ do (xs,p,f)<-unbind2' bp1 bf2; proc<-pr2bdw p; form<-form2bdw f; return $ "forall "++concat(Data.List.intersperse " " $ map show xs)++", sat "++proc++" "++form++"."
forall y1 x, sat (plus (taup (taup z)) (taup z)) (boxAct tau (disj (diaMatch x  y1 tt) (boxAct tau ff))).
*Main> putStrLn . runFreshM $ do (xs,p,f)<-unbind2' bp2 bf1; proc<-pr2bdw p; form<-form2bdw f; return $ "forall "++concat(Data.List.intersperse " " $ map show xs)++", sat "++proc++" "++form++"."
forall y1 x, sat (plus (match x y1 (taup (taup z))) (taup z)) (diaAct tau (diaAct tau tt)).
*Main>
```
The generated proposition (`forall y1 x, ...`) can be checked using Bedwyr as follows:
```
~/github/kyagrd/NonBisim2DF/pic$ rlwrap ./bedwyr pi_modal.def
[Warning] Now including "pi_modal.def".
[Warning] Now including "pi.def".
...
Bedwyr 1.4-beta13 (revision 1080) welcomes you.

For a little help, type "#help."

?= forall y1 x, sat (plus (taup (taup z)) (taup z)) (diaAct tau (diaAct tau tt)).
Found a solution.
More [y] ?
No more solutions (found 1).
?= forall y1 x, sat (plus (match x y1 (taup (taup z))) (taup z)) (boxAct tau (disj (diaMatch x  y1 tt) (boxAct tau ff))).
Found a solution.
More [y] ?
No more solutions (found 1).
?= forall y1 x, sat (plus (taup (taup z)) (taup z)) (boxAct tau (disj (diaMatch x  y1 tt) (boxAct tau ff))).
No solution.
?= forall y1 x, sat (plus (match x y1 (taup (taup z))) (taup z)) (diaAct tau (diaAct tau tt)).
No solution.
```
As expected, each distinguishing formula satisfies one of the processes but not the other.
The Bedwyr implementation of the OM formula checker is availiable at
https://github.com/kyagrd/NonBisim2DF/tree/master/pic


## Benchmark comparing with Bedwyr specifciation

```
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=100 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(0.02 secs, 6,648,424 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=250 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(0.07 secs, 34,298,168 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=500 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(0.18 secs, 129,581,456 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=750 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(0.28 secs, 302,031,952 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=1000 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(0.42 secs, 565,963,352 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=2500 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(1.95 secs, 3,404,646,784 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=5000 in bisim [] (foldr1 Plus (replicate n tau)) (foldl1 Plus (replicate n tau))
True
it :: Bool
(7.29 secs, 13,606,563,728 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt>
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt>
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=100 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(0.03 secs, 6,652,160 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=250 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(0.07 secs, 34,302,584 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=500 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(0.18 secs, 129,586,560 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=750 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(0.29 secs, 293,840,584 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=1000 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(0.41 secs, 539,324,432 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=2500 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(1.95 secs, 3,416,344,384 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=5000 in bisim [] (foldl1 Plus (replicate n tau)) (foldr1 Plus (replicate n tau))
True
it :: Bool
(7.35 secs, 13,609,904,424 bytes)
```

```
kyagrd@kyagrd:~/github/kyagrd/NonBisim2DF/pic$ rlwrap ./bedwyr a.def
[Warning] Now including "a.def".
[Warning] Now including "pi.def".
Bedwyr 1.4-beta13 (revision 1080) welcomes you.

For a little help, type "#help."

?= #time.
?= N = 100 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 929ms
Found a solution:
 N = 100
More [y] ?
+ 2ms
No more solutions (found 1).
?= N = 250 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 8123ms
Found a solution:
 N = 250
More [y] ?
+ 16ms
No more solutions (found 1).
?= N = 100 /\ exists P Q, getL N P /\ getR N Q /\ bisim P Q.
+ 889ms
Found a solution:
 N = 100
More [y] ?
+ 2ms
No more solutions (found 1).
?= N = 250 /\ exists P Q, getL N P /\ getR N Q /\ bisim P Q.
+ 8352ms
Found a solution:
 N = 250
More [y] ?
+ 25ms
No more solutions (found 1).
```
From 500, bedwyr takes too much memory.


```
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=6 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(0.19 secs, 85,158,592 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=7 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(0.58 secs, 401,238,832 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=8 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(2.23 secs, 1,935,709,936 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=9 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(9.78 secs, 9,526,100,024 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=10 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(46.39 secs, 47,643,823,728 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=5 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(0.07 secs, 18,662,216 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=6 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(0.20 secs, 85,152,328 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=7 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(0.58 secs, 401,240,728 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=8 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(2.21 secs, 1,935,709,936 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=9 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(9.68 secs, 9,526,100,656 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=10 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(46.85 secs, 47,643,826,104 bytes)

*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=11 in bisim [] (foldr1 Par (replicate n tau)) (foldl1 Par (replicate n tau))
True
it :: Bool
(232.05 secs, 241,255,012,128 bytes)
*Main IdSubLTS MemoUgly OpenBisim OpenLTS PiCalc SubstLatt> let n=11 in bisim [] (foldl1 Par (replicate n tau)) (foldr1 Par (replicate n tau))
True
it :: Bool
(231.54 secs, 241,255,012,440 bytes)
```

```
kyagrd@kyagrd:~/github/kyagrd/NonBisim2DF/pic$ rlwrap ./bedwyr b.def
[Warning] Now including "b.def".
[Warning] Now including "pi.def".
Bedwyr 1.4-beta13 (revision 1080) welcomes you.

For a little help, type "#help."

?= #time.
?= N = 5 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 399ms
Found a solution:
 N = 5
More [y] ?
+ 1ms
No more solutions (found 1).
?= N = 6 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 1277ms
Found a solution:
 N = 6
More [y] ?
+ 1ms
No more solutions (found 1).
?= N = 7 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 4293ms
Found a solution:
 N = 7
More [y] ?
+ 7ms
No more solutions (found 1).
?= N = 8 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 14714ms
Found a solution:
 N = 8
More [y] ?
+ 23ms
No more solutions (found 1).
?= N = 9 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 49396ms
Found a solution:
 N = 9
More [y] ?
+ 75ms
No more solutions (found 1).
?= N = 10 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
+ 161222ms
Found a solution:
 N = 10
More [y] ?
+ 224ms
No more solutions (found 1).
?= N = 11 /\ exists P Q, getR N P /\ getL N Q /\ bisim P Q.
[Error] At line 1, bytes 1-55: User interruption.
```
-->
