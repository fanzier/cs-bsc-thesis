\chapter{Nondeterminism Analysis}

The original motivation for introducing the language \salt{}
and its translation in \cite{orig} was
to derive free theorems for \cumin{}.
In order to do this, one has to restrict the nondeterministic behavior
of the functions involved.
\salt{} serves the purpose of making nondeterminism explicit
so that one can analyze it properly.
This chapter is about
how exactly this can be done.

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
It is a singleton set containing a function returning a singleton set,
so the original \cumin{} function |id| is completely deterministic.

In general, determining whether a function is deterministic is undecidable.
This can be proved by reduction from the halting problem.\footnote{
As \salt{} includes a simply-typed lambda calculus
and allows unrestricted recursion, it is Turing complete.}
Consider the following \salt{} expression.
> case condition of { True -> set True; False -> unknown<:Bool:>! }
This is deterministic if and only if always the first branch is evaluated.
However, we cannot decide whether |condition| is always |True|
since it is even undecidable whether its evaluation terminates at all.
So any method of detecting determinism will not be complete.
However, one can usually go quite far with purely syntactic transformations,
as I will describe below.

In what follows, I will not always strictly adhere to the \salt{} syntax
in order to keep the code readable.
For example, I will omit type instantiations if they are clear from the context
and I will allow additional infix operators to be defined.
Also, I will sometimes write
\salt{} function definitions in an equational style
instead of using explicit lambda abstractions.

The concept of \emph{semantic equivalence}, denoted by |~=|,
will be used extensively in this chapter.
It means that two expressions give the same results on evaluation.
A formal definition is given in \cite{orig}
and depends on the denotational semantics defined in the same paper.
As there is no space to develop this semantics here,
the reader will have to believe some claims
I make about certain semantic equivalences.
Most of the time, however, equational reasoning,
\eg with $\beta$-reduction or monad laws for sets,
will suffice to show the equivalences we are interested in.

\section{Useful Combinators}

In the rest of this chapter, the following \salt{} combinators will be useful.

> (.) :: (b -> c) -> (a -> b) -> (a -> c)
> (.) f g x = f (g x)
>
> set :: a -> Set a
> (set) x = { x }
>
> sMap :: (a -> b) -> Set a -> Set b
> sMap f s = s >>= set . f
The operator |(.)| is simply function composition.
I will often use the section notation for |(.)| as in Haskell:
|(f .)| stands for |\g -> f . g| and |(. f)| stands for |\g -> g . f|.
The function |sMap| has been mentioned earlier already.
It applies a function to each element of a set.
The combinator |set| places an expression in a singleton set.

Similarly to the monad laws for sets, the following laws hold for |sMap|.
\begin{enumerate}
\item |sMap f { e } ~= { f e }|
\item |sMap f s >>= g ~= s >>= (g . f)|
\item |s >>= (sMap f . g) ~= sMap f (s >>= g)|
\end{enumerate}
The proofs employ the monad laws.

> sMap f { e }
> ~= -- definition of |sMap|
> { e } >>= set . f
> ~= -- first monad law
> (set . f) e
> ~= -- definition of |(.)| and |set|
> { f e }

> sMap f s >>= g
> ~= -- definition of |sMap|
> (s >>= set . f) >>= g
> ~= -- third monad law
> s >>= (\x -> { f x } >>= g)
> ~= -- first monad law
> s >>= \x -> g (f x)
> ~= -- definition of |(.)|
> s >>= (g . f)

> s >>= (sMap f . g)
> ~= -- definition of |(.)|
> s >>= (\x -> sMap f (g x))
> ~= -- definiton of |sMap|
> s >>= (\x -> g x >>= (set . f))
> ~= -- third monad law
> (s >>= g) >>= (set . f)
> ~= -- definition of |sMap|
> sMap f (s >>= g)

Another concept to discuss is \emph{strictness}.
A \salt{} function |f :: tau' -> tau| is called strict
if |f failed<:tau':>! ~= failed<:tau:>!|.
Intuitively, this means that |f| evaluates its argument,
for example using a case expression.
Some transformations in the following only work for strict functions.
The functions |set|, |(f .)| and |sMap f| are strict
if |f| is, according to the semantics from \cite{orig}.

\section{Determinism}

First of all, we have to define what determinism means.
We will first do that for expressions that are not functions:
If |tau| is not a function type,
a \cumin{} expression |e :: tau| is called \emph{deterministic}
if there is a \salt{} expression |e' :: tytrans tau|
such that |trans e ~= {e'}|.
Such an |e'| is called a \emph{witness}.
This means that |e| is equivalent to a singleton set in \salt{}.
Note that according to the semantics from \cite{orig},
|failed<:Set tau:>! ~= { failed<:tau:>! }| holds.
Hence, a failed computation can also be regarded as a singleton set.

Transferring this to the operational semantics,
it means that there is at most one successful evaluation for |e|,
in particular, the evaluation of |e| is allowed to fail.
A sufficient (not necessary) condition for at most one evaluation
is that the Guess rule from the operational semantics is never used.
This is essentially what we will try to show
when proving an expression deterministic in the following.
The condition is not necessary
since evaluating |last<:Bool:> [True]|,
with the function |last| from the introduction,
uses the Guess rule due to logic variables,
but the expression still has only one result: |True|.

How can one derive that an expression is deterministic without evaluating it?
It can often be done by inlining top-level functions
(replacing them by the right-hand side of their definition)
and applying the monad laws for sets.

For instance, consider the \cumin{} expression |double (double 1)|.
To show that it is deterministic,
one translates the expression to \salt{},
simplifies the result
and inlines functions to apply more monad laws.
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

As another example, consider the \cumin{} expression |guard<:Nat:> cond 1|
where |cond| is some deterministic expression
and the function |guard| returns its second argument
if and only if the first argument is |True|:
> guard :: forall a. Bool -> a -> a
> guard cond x = case cond of { True -> x; False -> failed<:a:> }

For this instance, another rule is useful:
In a case expression where each branch is a singleton set,
this singleton set can be extracted and moved out of the case expression:
> case e of { p_1 -> { e_1 }; ..; p_n -> { e_n } }
> ~= { case e of { p_1 -> e_1; ..; p_n -> e_n } }
Even more generally, the following transformation is valid
for strict functions |h :: tau' -> Set tau|.
> case e of { p_1 -> h e_1; ..; p_n -> h e_n }
> ~= h case e of { p_1 -> e_1; ..; p_n -> e_n }
Strictness of |h| is necessary
because, if |e| fails, so will the case expression.
For the equivalence to hold in this case, |h| also has to fail.
Again, a formal proof requires the semantics from \cite{orig}.

Using this additional rule, one can show
that |guard<:Nat:> cond 1| is equivalent to a singleton set.
> trans (guard<:Nat:> cond 1)
> ~= -- translation and simplification
> guard<:Nat:> >>= \g -> trans cond >>= \c -> g c >>= \g' -> g' 1
> ~= -- assumption: |cond| is deterministic
> guard<:Nat:> >>= \g -> { cond' } >>= \c -> g c >>= \g' -> g' 1
> ~= -- first monad law, $\beta$-reduction
> guard<:Nat:> >>= \g -> g cond' >>= \g' -> g' 1
> ~= -- inlining |guard|
> {\cond -> {\x -> case cond of { True -> { x }; False -> { failed<:Nat:> } } } }
>   >>= \g -> g cond' >>= \g' -> g' 1
> ~= -- case rule
> {\cond -> {\x -> {case cond of { True -> x; False -> failed<:Nat:> } } } }
>   >>= \g -> g cond' >>= \g' -> g' 1
> ~= -- first monad law, $\beta$-reduction
> {\x -> {case cond' of { True -> x; False -> failed<:Nat:> } } } >>= \g' -> g' 1
> ~= -- first monad law, $\beta$-reduction
> { case cond' of { True -> 1; False -> failed<:Nat:> } }
This is again a singleton set,
\ie under the assumption that |cond| is deterministic,
so is |guard<:Nat:> cond 1|.

As the next step, let us define determinism for functions.
A \cumin{} expression |f :: tau_1 -> tau_2| is called \emph{deterministic}
if there is a \salt{} function |f' :: tytrans tau_1 -> tytrans tau_2|
such that |trans f ~= { set . f' }|.
(Recall that |trans f :: Set (tau_1 -> Set tau_2)|.)
Again, |f'| is called a \emph{witness}.
Not only does this mean that |trans f| is a singleton set,
but this also implies
that applying this single function
to any \salt{} expression of type |tytrans tau_1|
yields a singleton set.

Operationally speaking, this means
that there is at most one successful evaluation
when applying |f| to any deterministic expression of type |tau_1|.

Although the methods are the same as for deterministic expressions,
let us look at how functions can be proved deterministic.
Consider the \cumin{} function |double| as an example.
One can see that in this case, a witness is given by |\x :: Nat -> x + x|.
> trans double
> ~= -- translating to \salt{} and symplifying
> double
> ~= -- inlining |double|
> { \x :: Nat -> { x + x } }
> ~= -- rewriting using |set| ($\beta$-expansion)
> { set . (\x :: Nat -> x + x) }

\section{Multideterminism}

We will now consider a weaker notion of determinism, given in \cite{orig}.
A \cumin{} expression |f :: tau_1 -> tau_2| is called \emph{multideterministic}
if there is a \salt{} function |f' :: Set (tytrans tau_1 -> tytrans tau_2)|
such that |trans f ~= sMap (\g -> set . g) f'|.
Again, such an |f'| is called a \emph{witness}.

Intuitively, this means that the set braces on the inner level of
|trans f :: Set (tytrans tau_1 -> Set (tytrans tau_2))|
are actually unnecessary,
\ie |trans f| represents a set of functions returning singleton sets.
The motivation for this definition in \cite{orig}
is the derivation of free theorems,
which requires the inner level of nondeterminism to be restricted.

Operationally, one can think of multideterminism as follows.
When applying |f| to a deterministic \cumin{} expression |e|,
|f| has to be in flat normal form at some point.
The Apply rule may be used to achieve this.
Since |f| is not required to be deterministic,
there may be more than one flat normal form
since |f| is represented by a set of functions in \salt{}.
However, once a flat normal form is obtained,
there must be at most one evaluation result for the function application.

The definition and properties of |sMap| from above are useful
in order to prove that functions are multideterministic.
To give a concrete example,
let us show that |maybeDouble1| from \cref{sec:pecularities}
is multideterministic.
Recall the \cumin{} definitions:
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
We now want to analyze the \salt{} function |maybeDouble1|
and try to find a witness for its multideterminism.
First, we inline |choose|.
> maybeDouble1 = id<:Nat:> >>= \i ->
>   double >>= \d ->
>   unknown<:Bool:> >>= \b ->
>   case b of { True -> { i }; False -> { d } }
Inlining |id| and |double|, followed by simplifications with monad laws, yields:
> unknown<:Bool:> >>= \c ->
>   case c of { True -> { \x -> { x } }; False -> { \x -> { x + x } } }
> ~= -- since |sMap f {e} = {f e}|
> unknown<:Bool:> >>= \c ->
>   case c of { True -> sMap (set .) { \x -> x }; False -> sMap (set .) { \x -> x + x } }
> ~= -- case rule
> unknown<:Bool:> >>= \c ->
>   sMap (set.) (case c of { True -> { \x -> x }; False -> { \x -> x + x } })
> ~= -- rewrite with |(.)|
> unknown<:Bool:> >>= (sMap (set.) . (\c ->
>   case c of { True -> { \x -> x }; False -> { \x -> x + x } }))
> ~= -- since |s >>= (sMap f . g) ~= sMap f (s >>= g)|
> sMap (set .)
>   (unknown<:Bool:> >>= \c -> case c of { True -> { \x -> x }; False -> { \x -> x + x } })
For the case rule, we used that |sMap (set .)| is strict,
which follows from the semantics in \cite{orig}.
The witness |unknown<:Bool:> >>= \c -> case c of { .. }|
represents the set $\{ |\x -> x|, |\x -> x + x| \}$
of two deterministic functions.
This shows that |maybeDouble1| is multideterministic.
On the other hand, such a proof fails for |maybeDouble2|,
which is another illustration of their discrepancy.

\section{Recursive Definitions}
\label{sec:nda-rec}

From what we discussed before,
it is not clear how to handle recursion.
For illustration, consider the infinite list:
> ones :: List Nat
> ones = Cons<:Nat:> 1 ones
Intuitively, it is clear that this is deterministic
but our methods from before (especially inlining) will not work.
Let us look at the \salt{} code.
> ones :: Set (List Nat)
> ones = ones >>= \x -> { Cons<:Nat:> 1 x }
At first sight,
it seems that there is no way
to \enquote{extract} any singleton sets from this.
However, I claim that it is equivalent to the following.
> ones' :: List Nat
> ones' = Cons<:Nat:> 1 ones'
>
> ones :: Set (List Nat)
> ones = { ones' }

To justify this transformation, consider the following more general scenario.
We have a recursive, set-typed function definition |f|.
> f :: Set tau
> f = e
This can be rewritten as |f = g f|
for some non-recursive function |g :: Set tau -> Set tau|,
namely |g := \x -> e[x/f]| where |x| is a fresh variable.
Moreover, suppose we know that |g . h ~= h . g'|
for some |g' :: tau' -> tau'| and |h :: tau' -> Set tau|
where |h| is \emph{strict},
\ie |h failed<:tau':>! ~= failed<:Set tau:>!|.
Under these circumstances, |f| can be defined like this.
> f :: Set tau
> f = h f'
>
> f' :: tau'
> f' = g' f'
This transformation is known as \emph{fixed point fusion} \cite{fixpoint}.
A proof of this rule for \salt{}
would again rely on the semantics from \cite{orig}.
To give some intuition, consider the following argument.
The definition of |f = g f| should be the \enquote{limit} of
|g failed<:Set tau:>!|, |g (g failed<:Set tau:>!)|, |g (g (g failed<:Set tau:>!))| etc.
If one knows that |g . h ~= h . g'|,
one can reason as follows.
> g (.. (g failed<:Set tau:>!) ..)
> ~= -- strictness of |h|
> g (.. (g (h failed<:tau':>!)) ..)
> ~= -- since |g . h ~= h . g'|
> g (.. h (g' failed<:tau':>!) ..)
> ~= -- \dots iterating \dots
> ~= h (g' (.. (g' failed<:tau':>!) ..))
So |f| is equivalent to the \emph{limit} of
|h (g' failed<:tau':>!)|, |h (g' (g' failed<:tau':>!))| etc.,
which means it is equivalent to |f| defined as |f = h f'| where |f' = g' f'|.

In the concrete example above, we can choose
|g := \y -> y >>= \x -> { Cons<:Nat:> 1 x }|
to satisfy |ones = g ones|.
Furthermore one can show the following.
> g . set
> ~= \y -> { y } >>= \x -> { Cons<:Nat:> 1 x }
> ~= \y -> { Cons<:Nat:> 1 y }
> ~= set . Cons<:Nat:> 1
So choosing |g' = Cons<:Nat:> 1| and |h = set|
allows exactly the transformation we did above.
The required strictness of |set|
is a consequence of the semantics in \cite{orig}.

Let us consider another example: the |length| function in \cumin{}.
> length :: forall a. List a -> Nat
> length list = case list of
>   Nil -> 0
>   Cons x xs -> 1 + length<:a:> xs
Translating it to \salt{} yields the following function, after simplification.
> length :: forall a. Set (List a -> Set Nat)
> length = {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> length<:a:> >>= \f ->
>     f xs >>= \l -> { 1 + l}}
One can \enquote{factor out} a non-recursive function |g| again.
> length :: forall a. Set (List a -> Set Nat)
> length = g length
>
> g :: forall a. Set (List a -> Set Nat) -> Set (List a -> Set Nat)
> g = \length' -> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> length' >>= \f ->
>     f xs >>= \l -> { 1 + l}}
As before, one can show an \enquote{extraction property} of |g|:
> g . (set . (set .))
> ~= -- definition of |(.)|, $\beta$-reduction
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> {set . length'} >>= \f ->
>     f xs >>= \l -> { 1 + l}}
> ~= -- first monad law
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> {length' xs} >>= \l -> { 1 + l}}
> ~= -- first monad law
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> { 1 + length' xs}}
> ~= -- case rule
> \length' :: (List a -> Nat) ->
> {\list :: List a -> {case list of
>   Nil -> 0
>   Cons x xs -> 1 + length' xs } }
> ~= -- rewrite with combinators
> (set . (set .)) . (\length' :: (List a -> Nat) ->
> \list :: List a -> case list of
>   Nil -> 0
>   Cons x xs -> 1 + length' xs)
> ~= -- choosing |g'| suitably
> (set . (set .)) . g'
Using fixed point fusion with |h = set . (set .)| and |g'|,
we can equivalently define |length = { set . length'}|
with |length' = g' length'|.
Again, the strictness of |h| follows from the semantics in \cite{orig}.
Inlining |g'| yields:
> length' :: List a -> Nat
> length' = \list :: List a -> case list of
>   Nil -> 0
>   Cons x xs -> 1 + length' xs
>
> length :: Set (List a -> Set Nat)
> length = { \list :: List a -> { length' list } }
In this equivalent definition,
it is obvious that |length| is deterministic.
Furthermore, this is the optimal way of writing |length|
and it was derived from the original translation
using only well-specified program transformations.

So far, we only considered directly recursive functions.
But the transformation can easily be adapted
to mutually recursive functions.
For instance, say there are to functions |f| and |g|,
recursively calling each other.
Then one creates two new functions |f'| and |g'|
that are mutually recursive.
This works the same for three functions etc.

\section{Limitations and Related Work}

While I have presented methods to analyze lots of functions,
including recursive ones,
I have not talked about functions with higher order arguments,
like |map|.
Whether such a function is deterministic can depend on
whether its higher order argument is deterministic or not.
So this has to be decided at the call site.
Inlining can often solve this problem,
but in case of recursive functions,
it does not help.

There are other ways to analyze nondeterminism
that do not rely on syntactic transformations.
For instance, a type and effect system can be used
to track the nondeterminism in the program.
Such an approach is described in \cite{nondetana}.

However, the goal in this thesis was to analyze
the nondeterminism behavior of programs by translating them to \salt{}
and applying program transformations.
While there are some limitations,
many \cumin{} expressions and functions
can be shown to be (multi-)deterministic,
using the general rules described in this chapter.
