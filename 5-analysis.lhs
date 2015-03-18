\chapter{Nondeterminism Analysis}

The original motivation for introducing the language \salt{}
and its translation in \cite{orig} was
to derive free theorems for \cumin{}.
In order to do this, one has to restrict the nondeterministic behavior
of the functions involved.
\salt{} serves the purpose of making nondeterminism explicit
so that one can analyze it properly.
This chapter is about
how exactly this is done.

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
This can be proved by reduction from the halting problem.\footnote{
As \salt{} includes a simply-typed lambda calculus
and allows unrestricted recursion, it is Turing complete.}
Consider the following \salt{} expression:
> case condition of { True -> set True; False -> unknown<:Bool:>! }
This is deterministic if and only if the first branch is always evaluated.
However, we cannot decide whether |condition| is always |True|
since it is even undecidable whether its evaluation terminates at all.
So any method of detecting determinism must be conservative
and will not be complete.
However, one can go quite far with purely syntactic transformations.

In the following, I will not strictly adhere to the \salt{} syntax
to keep it readable.
For example, I will omit type instantiations if they are obvious
and I will allow additional infix operators.
Also, I will sometimes write
\salt{} function definitions in an equational style
instead of explicit lambda abstractions.

\section{Determinism}

First of all, we have to define what deterministic means.
A \cumin{} expression |e :: tau| is called \emph{deterministic}
if there is a \salt{} expression |e' :: tytrans tau|
such that |trans e ~= {e'}|.
As before, |~=| denotes semantical equivalence.
So this means that |e| is equivalent to a singleton set in \salt{}.

How can one derive that an expression is deterministic?
It can often be done by inlining top-level functions
(replacing them by the right-hand side of their definition)
and applying the monad laws for sets.

For instance, consider the expression |double (double 1)|.
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

As another example, consider the expression |guard<:Nat:> cond 1| where
|cond| is some deterministic expression and
> guard :: forall a. Bool -> a -> a
> guard cond x = case cond of { True -> x; False -> failed<:a:> }
returns |x| only if |cond| is |True|.
Here, another rule is useful:
In a case expression where each branch is a singleton set,
this singleton set can be extracted and moved out of the case expression:
> case e of { p_1 -> { e_1 }; ..; p_n -> { e_n } }
> ~= { case e of { p_1 -> e_1; ..; p_n -> e_n } }
This transformation works because |set| has strict semantics in \salt{}.
(A formal proof would need the denotational semantics for \salt{}
and there is no space to develop it here.)
Using these rules, one can show
that |guard<:Nat:> cond 1| is equivalent to a singleton set.
> trans (guard<:Nat:> cond 1)
> ~= -- translation and simplification
> guard<:Nat:> >>= \g -> trans cond >>= \c -> g >>= \g' -> g' c 1
> ~= -- assuption: |cond| is deterministic
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
This is again a singleton set,
\ie under the assumption that |cond| is deterministic,
so is |guard<:Nat:> cond 1|.

\section{Multideterminism}

In the following, I will study a weaker notion of determinism,
namely \emph{multideterminism}.
For that, the following comibinators are needed.\footnote{
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
I will often use the section notation for |(.)| as in Haskell:
|(f .)| stands for |\g -> f . g| and |(. f)| stands for |\g -> g . f|.

Using these combinators,
a \cumin{} function |f :: tau_1 -> tau_2| is called \emph{multideterministic}
if there is a \salt{} function |f' :: Set (tytrans tau_1 -> tytrans tau_2)|
such that |trans f ~= sMap (\g -> set . g) f'|.
Such an |f'| is called a \emph{witness}, as in \cite{orig}.

Intuitively, this means that the set braces on the inner level of
|trans f :: Set (tytrans tau_1 -> Set (tytrans tau_2))|
are unnecessary,
\ie |f| represents a set of functions returning singleton sets.
The motivation for this definition in \cite{orig}
is the derivation of free theorems,
which requires the inner level of nondeterminism to be restricted.

Besides the definition of |sMap|,
the following equivalences are useful.
\begin{enumerate}
\item |sMap f { e } ~= { f e }|
\item |sMap f s >>= g ~= s >>= (g . f)|
\item |s >>= (sMap f . g) ~= sMap f (s >>= g)|
\end{enumerate}
The proofs employ the monad laws.
\begin{enumerate}
\item
> sMap f { e }
> ~= -- definition of |sMap|
> { e } >>= set . f
> ~= -- first monad law
> (set . f) e
> ~= -- definition of |(.)|
> { f e }
\item
> sMap f s >>= g
> ~= -- definition of |sMap|
> (s >>= set . f) >>= g
> ~= -- third monad law
> s >>= (\x -> { f x } >>= g)
> ~= -- first monad law
> s >>= \x -> g (f x)
> ~= -- definition of |(.)|
> s >>= (g . f)
\item
> s >>= (sMap f . g)
> ~= -- definition of |(.)|
> s >>= \x -> sMap f (g x)
> ~= -- definiton of |sMap|
> s >>= \x -> g x >>= (set . f)
> ~= -- third monad law
> s >>= g >>= (set . f)
> ~= -- definition of |sMap|
> sMap f (s >>= g)
\end{enumerate}

To give a concrete example,
let us show that |maybeDouble1| from the beginning of Chapter 3
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

\section{Recursive Definitions}

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

To justify that, we need to look at
how \salt{} defines the semantics of recursion.
A recursive set-typed definition |f = e| can be rewritten as |f = g f|
(the least fixpoint of |g|)
for some non-recursive function |g|, namely |g := \x -> e[x/f]|.
By the denotational semantics for \salt{},
|f| is equivalent to the union of
|g failed|, |g (g failed)|, |g (g (g failed))| etc.
If one knows that |g . set ~= set . g'|,
one can write
> g (.. (g failed) ..) ~= g (.. (g {failed}) ..) ~= g (.. {g' failed} ..)
>   ~= .. ~= {g' (.. (g' failed) ..)}
because |failed<:Set tau:>! = { failed<:tau:>! }| for all |tau|
since |set| has strict semantics.
So |f| is equivalent to the union of
|set (g' failed)|, |set (g' (g' failed))| etc.,
which means it is equivalent to |f| defined as |f = set (g' f)|.

\todo[inline]{Is that sufficient as an explanation?}
\todo[inline]{Use explicit |fix| combinator? Or is that unnecessary?}

In the concrete example above, we can choose
|g := \y -> y >>= \x -> { Cons<:Nat:> 1 x }|
to satisfy |ones = g ones|.
Furthermore one can show that
> g . set
> ~= \y -> { y } >>= \x -> { Cons<:Nat:> 1 x }
> ~= \y -> { Cons<:Nat:> 1 y }
> ~= set . Cons<:Nat:> 1
So choosing |g' = Cons<:Nat:> 1| allows exactly the transformation
we did above.

Let us consider another example: the |length| function.
> length :: forall a. List a -> Nat
> length list = case list of
>   Nil -> 0
>   Cons x xs -> 1 + length<:a:> xs
Translated to \salt{}:
> length :: forall a. Set (List a -> Set Nat)
> length = {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> length<:a:> >>= \f ->
>     f xs >>= \l -> { 1 + l xs}}
or equivalently:
> length :: forall a. Set (List a -> Set Nat)
> length = g length
>
> g :: forall a. Set (List a -> Set Nat) -> Set (List a -> Set Nat)
> g = \length' -> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> length' >>= \f ->
>     f xs >>= \l -> { 1 + l xs}}

Again, one can show an \enquote{extraction property} of |g|:
> g . (set . (set .))
> ~= -- definition of |(.)|, $\beta$-reduction
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> {set . length'} >>= \f ->
>     f xs >>= \l -> { 1 + l xs}}
> ~= -- first monad law
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> {length' xs} >>= \l -> { 1 + l xs}}
> ~= -- first monad law
> \length' :: (List a -> Nat) ->
> {\list :: List a -> case list of
>   Nil -> { 0 }
>   Cons x xs -> { 1 + length' xs}}
> ~= -- case
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
So, we can equivalently define |length = { set . length'}|
with |length' = g' length'|.
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

\section{Limitations and Further Work}

While I have presented methods to analyze lots of functions,
including recursive ones,
I have not talked about functions with higher order arguments,
like |map|.
Whether such a function is deterministic depends on
whether its higher order argument is deterministic or not.
So it has to be decided at the call site.
Inlining can solve that problem
but in case of recursive functions,
it does not help.
One could instead create a special function |map_f|
for every call of |map f| occuring in the program,
and replace the recursive calls to |map f| by |map_f|.
In |map_f| one could then inline |f|
and use the methods from above.
However, if the recursive call uses a modified function,
\ie not |f| again
but say |f| composed with another function,
this cannot be easily repaired.
Even if it works, it is quite complicated.

To avoid this complexity, it is probably better
to use a type and effect system to track the nondeterminism in the program.
Such an approach is described in \cite{nondetana}.

However, the goal in this thesis was to analyze
the nondeterminism behavior of programs by translating them to \salt{}
and applying program transformations.
The methods I described here can be formalized
and I even implemented them.
This implementation is able to analyze the nondeterminism of all the functions
we discussed in this chapter.
However, the details were quite technical and the proofs relatively long,
so I did not include it here.
The transformations I described could also be used
to generate better \salt{} code from \cumin{} programs.
