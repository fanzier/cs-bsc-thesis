\chapter{Nondeterminism Analysis}

The original motivation for introducing the language \salt{}
and its translation in \cite{orig} was
to derive free theorems for \cumin{}.
In order to do this, one has to restrict the nondeterministic behavior
of the functions involved.
\salt{} serves the purpose of making nondeterminism explicit
and being able to analyze it properly.
This topic, namely nondeterminism analysis, is what this chapter is about.

\section{Introduction}

It was mentioned before that a \salt{} function
whose signature contains no set types will be completely deterministic
because all nondeterminism is marked with |Set|.
On the other hand, the translation routine from the previous chapter
always produces set-typed expressions
even if they are in fact deterministic.
Set-typed functions are deterministic
if they only return singleton sets.
As a trivial example, consider the translated identity function.
> id :: forall a. Set (a -> Set a)
> id = { \ x -> { x } }
|id| is a singleton set containing a function returning a singleton set,
so it is completely deterministic.

What is also quite obvious is
that deciding whether a function is deterministic is undecidable.
This can be proved by reduction from the halting problem:
> test :: Set Bool
> test = case condition of { True -> set True; False -> unknown<:Bool:> }
This is deterministic if and only if |condition| is true.
However, in general it is undecidable which branch is evaluated.
After all, we cannot even decide whether |condition| terminates.
So any method of detecting determinism must be conservative
and will not be complete.
However, one can go quite far with purely syntactic transformations.

\section{Determinism}

First of all, we have to define what deterministic means.
A \cumin{} expression |e| is called deterministic
if there is a \salt{} expression |e'|
such that |trans e ~= {e'}|.

How can one derive that an expression is deterministic?
It can often be done by inlining top-level functions
(replacing them by the right-hand side of their definition)
and applying the monad laws for sets.

For instance, consider the expression |double (double 1)|.
To show that it is deterministic,
one translates the expression to \salt{},
simplifies the result
and inlines functions to apply more monad laws.
(Types in lambda abstractions are omitted for clarity.)
> trans (double (double 1))
> ~= -- translation and simplification:
> double >>= \f -> (double >>= \g -> g 1) >>= f
> ~= -- inlining |double|:
> {\x -> {x + x}} >>= \f -> ({\x -> {x + x}} >>= \g -> g 1) >>= f
> ~= -- first monad law:
> {\x -> {x + x}} >>= \f -> ((\x -> {x + x}) 1) >>= f
> ~= -- $\beta$-reduction
> {\x -> {x + x}} >>= \f -> { 1 + 1 } >>= f
> ~= -- first monad law and $\beta$-reduction:
> { 1 + 1 } >>= \x -> { x + x }
> ~= -- first monad law and $\beta$-reduction:
> { (1 + 1) + (1 + 1) }
This is a singleton set,
so the original expression is deterministic.
Note that we did not have to evaluate the expression completely
to recognize that.

As another example, consider the expression |guard<:Nat:> cond 1| where
|cond| is some deterministic expression and
> guard :: forall a. Bool -> a -> a
> guard cond x = case cond of { True -> x; False -> failed<:a:> }
returns |x| only if |cond| is |True|.
Here, another rule is useful:
In a case expression where each branch is a singleton set,
this singleton set can be extracted and moved out of the case expression.
These two transformations work because |set| has strict semantics in \salt{}.
A formal prove needs the denotational semantics for \salt{}
and there is no space to develop it here.
Using these rules, one can show it is equivalent to a singleton set.
> trans (guard<:Nat:> cond 1)
> ~= -- translation and simplification
> guard<:Nat:> >>= \g -> trans cond >>= \c -> g >>= \g' -> g' c 1
> ~= -- |cond| is deterministic
> guard<:Nat:> >>= \g -> { cond' } >>= \c -> g >>= \g' -> g' c 1
> ~= -- first monad law, $\beta$-reduction
> guard<:Nat:> >>= \g -> g >>= \g' -> g' cond' 1
> ~= -- inlining |guard|
> {\cond -> {\x -> case cond of { True -> { x }; False -> { failed<:Nat:> } } } }
>   >>= \g -> g >>= \g' -> g' cond' 1
> ~= -- case rule
> {\cond -> {\x -> {case cond of { True -> x; False -> failed<:Nat:> } } } }
>   >>= \g -> g >>= \g' -> g' cond' 1
> ~= -- first monad law, $\beta$-reduction
> {\x -> {case cond' of { True -> x; False -> failed<:Nat:> } } } >>= \f -> f 1
> ~= -- first monad law, $\beta$-reduction
> { case cond' of { True -> 1; False -> failed<:Nat:> } }

\section{Multideterminism}

In the following, I will study a weaker notion of determinism,
namely \emph{multideterminism}.
For that, the following comibinatiors are needed.\footnote{
I take the liberty to write functions in an equational style for readability
although this is technically not allowed by the \salt{} syntax.}
> (.) :: (b -> c) -> (a -> b) -> (a -> c)
> (.) f g x = f (g x)
>
> set :: a -> Set a
> (set) x = { x }
>
> sMap :: (a -> b) -> Set a -> Set b
> sMap f s = s >>= set . f
|(.)| is just function composition,
|sMap| applies a function to each element of a set
and |set| places an expression in a singleton set.

Using these combinators,
a \cumin{} function |f :: tau_1 -> tau_2| is called \emph{multideterministic}
if there is a \salt{} function |f' :: Set (tytrans tau_1 -> tytrans tau_2)|
such that |trans f ~= sMap (\g -> set . g) f'|.
Such an |f'| is called a \emph{witness}. \cite{orig}

Intuitively, this means that the set braces on the inner level of
|trans f :: Set (tytrans tau_1 -> Set (tytrans tau_2))|
are unnecessary,
\ie |f| represents a set of functions returning singleton sets.
The motivation for this definition in \cite{orig}
is the derivation of free theorems,
which require the inner level of nondeterminism to be restricted.

Besides the definition of |sMap|,
the following equivalence is useful.
\begin{itemize}
\item |sMap f s >>= g ~= s >>= (g . f)|
\item |s >>= (sMap f . g) ~= sMap f (s >>= g)|
\end{itemize}
The proofs employ the monad laws.
> sMap f s >>= g
> ~= -- definition of sMap
> (s >>= set . f) >>= g
> ~= -- third monad law
> s >>= (\x -> { f x } >>= g)
> ~= -- first monad law
> s >>= \x -> g (f x)
> ~= -- definition of |(.)|
> s >>= (g . f)
>
> s >>= (sMap f . g)
> ~= -- definition of |(.)|
> s >>= \x -> sMap f (g x)
> ~= -- definiton of |sMap|
> s >>= \x -> g x >>= (set . f)
> ~= -- third monad law
> s >>= g >>= (set . f)
> ~= -- definition of |sMap|
> sMap f (s >>= g)

To give a concrete example,
let us show that |maybeDouble1|from the beginning of Chapter 3
is multideterministic.
Recall the definitions:
> maybeDouble1 :: Nat -> Nat
> maybeDouble1 = choose<:Nat -> Nat:> id<:Nat:> double
>
> choose :: forall a. a -> a -> a
> choose x y = let b :: Bool free in case b of { True -> x; False -> y }
Their \salt{} translations look like this after simplification:
> maybeDouble1 :: Set (Nat -> Set Nat)
> maybeDouble1 = choose<:Nat -> Set Nat:> >>= \c ->
>   id<:Nat -> Set Nat:> >>= \i ->
>   c i >>= \cc ->
>   double >>= \d ->
>   cc d
> choose :: forall a. Set (a -> Set (a -> Set a))
> choose = {\x -> {\y -> unknown<:Bool:> >>= \c ->
>   case c of { True -> { x }; False -> { y } } } }
Inlining |choose| and simplifying yields:
> maybeDouble1 = id<:Nat:> >>= \i ->
>   double >>= \d ->
>   unknown<:Bool:> >>= \b ->
>   case b of { True -> { i }; False -> { d } }
Inlining |id| and |double|, followed by simplification, yields:
> unknown<:Bool:> >>= \c ->
> case c of { True -> { \x -> { x } }; False -> { \x -> { x + x } } }
> ~= -- since |sMap f {e} = {f e}|
> unknown<:Bool:> >>= \c ->
> case c of { True -> sMap (set .) { \x -> x }; False -> sMap (set .) { \x -> x + x } }
> ~= -- case rule
> unknown<:Bool:> >>= \c ->
> sMap (set.) (case c of { True -> { \x -> x }; False -> { \x -> x + x } })
> ~= -- rewrite with |(.)|
> unknown<:Bool:> >>= (sMap (set.) . (\c ->
> case c of { True -> { \x -> x }; False -> { \x -> x + x } }))
> ~= -- since |s >>= (sMap f . g) ~= sMap f (s >>= g)|
> sMap (set .) (unknown<:Bool:> >>= \c -> case c of { .. })
This shows that |maybeDouble1| is multideterministic.
On the other hand, such a proof fails for |maybeDouble2|,
which is another illustration of their discrepancy.

\todo[inline]{Discuss recursive functions?}
\todo[inline]{Discuss problems with higher-order functions}
