# My Bachelor's Thesis on Functional-Logic Programming Languages

This thesis ([PDF](thesis.pdf)) deals with functional logic languages.
These languages combine the strengths of functional (like Haskell, ML) and logic languages (like Prolog).

The two languages of interest are *CuMin* and *SaLT*, introduced in [1].
I implemented an operational semantics for CuMin (i.e. an interpreter)
and an optimizing compiler [3] to the lower-level SaLT language.
I also describe ways to reason about nondeterminism in CuMin and SaLT programs.

[1] Stefan Mehner et al. ["Parametricity and Proving Free Theorems for Functional-Logic
Languages"](http://www.janis-voigtlaender.eu/MSSV14.html)

[2] The code is in another repository: https://github.com/fanzier/cumin-operational

[3] The translation code: https://github.com/fanzier/cumin2salt
