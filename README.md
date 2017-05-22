# hs-picalc-unbound-example

This directory contains literate Haskell program that is both a source code
of a program and of a document.

## to build the document
To compile the document you need [lhs2TeX](http://hackage.haskell.org/package/lhs2tex),
which preprocesses literate Haskell programs into LaTeX files.
On debian or ubuntu linux, you can install this by
```
sudo apt-get install lhs2tex
```
Then you can run "make" to build the documnet.

## to build the Haskell program

Install [`stack`](https://www.haskellstack.org/), which is a toolset for Haskell
including a sandboxing build system. It can be installed
on debian by ``sudo apt-get install stack`` and
on ubuntu by ``sudo apt-get install haskell-stack``.
After installing stack, make sure that your ``PATH`` environment variable
includes ``$HOME/.local/bin`` where ``$HOME`` is the path to your home directory.
To make sure that everything is up to date and also install a basic utility:
```k
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
