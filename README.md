# hs-picalc-unbound-example

This directory contains literate Haskell program that is both a source code
of a program and of a document.

## to build the document
To compile the document you need lhs2TeX, which preprocesses
literate Haskell programs into LaTeX files.
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
