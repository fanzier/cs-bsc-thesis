\chapter{Conclusion}

In this thesis,
I have explained and implemented an operational semantics for \cumin{}.
The semantics helps to understand intricacies of \cumin{}'s evaluation,
such as call-time choice.
In the implementation, the actual evaluation and nondeterminism are separated
by lazily constructing a computation tree
with all the possible nondeterministic results
and then traversing it with either breadth-first or depth-first search,
optionally limited to a certain depth.
In most cases, breadth-first search seems to be the best option
since it is complete
and the performance is similar to depth-first search.

Moreover, I have described and implemented
a translation from \cumin{} to \salt{}.
Superfluous sets in the generated \salt{} code
can often be eliminated using monad laws.
Further simplifications are possible
by making use of $\beta$- and $\eta$-reduction.
I measured the performance difference between
the optimized and unoptimized \salt{} code,
using the denotational semantics implemented by Fabian Thorand.
In all test cases, the simplified code was significantly faster.

Finally, the translation procedure was used
to better understand the nondeterminism of \cumin{} programs.
To this end, I demonstrated by way of examples
some general syntactic transformations
that \enquote{extract} singleton sets from the corresponding \salt{} code.
Again, monad laws and $\beta$-reduction are useful,
together with inlining of function definitions.
The notion of multideterminism was defined, using the |sMap| combinator,
and it was demonstrated how multideterministic functions can be analyzed.
I also addressed recursive functions,
for which inlining is not an option.
However, by means of the fixpoint fusion rule,
one can prove for many recursive functions
that they are (multi-)deterministic as well.
