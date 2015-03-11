\chapter{Preliminaries}

In this chapter,
I will give a more precise description of \cumin{} and \salt{},
as well as some remarks on the implementation of parsers and type checkers,
which was done together with Fabian Thorand.

\section{Notation and Conventions}

In the following,
a sequence of objects |z_1 .. z_n| will be denoted |vec z_n|.
If the index is unclear,
it is written |((vec z_n))<:n:>|,
or even $|((vec z_n))|_{n \in S}$
where $S$ denotes the range of $n$.
|e[y/x]| means replacing every occurence of |x| in |e| with |y|.
By convention,
|alpha, beta| denote type variables,
|rho, tau| denote types,
|x,y| denote variables,
|m,n| denote natural numbers,
|p| denotes a pattern in pattern matches,
|e| denotes an expression,
|f| denotes a function,
|C| denotes a constructor,
|A| denotes an algebraic data type, and
|Gamma| denotes a context,
unless otherwise stated.

When specifying the well-formedness, evaluation or other \emph{judgments}
about programs, types or expressions,
the following notation is widely used.

\[
\AxiomC{Assumption 1}
\AxiomC{Assumption 2}
\AxiomC{\dots}
\TrinaryInfC{Consequence}
\DisplayProof
\]

This means that the consequence is a valid judgment
if all the assumptions can be shown to be valid judgments.
Oftentimes, these judgments will only make sense in a certain \emph{context},
denoted |Gamma|.
The judgment is then written with the turnstile symbol:
$\Gamma \vdash \text{judgment}$.

\section{Types in \cumin{} and \salt{}}

Types can either be a type variable
or a type constructor applied to a number of types,
which must always be fully applied.
A type constructor is one of the following.
\begin{itemize}
\item The name of a custom algebraic data type
\item |->|, the function type constructor, with two arguments.
It associates to the right.
\item |Nat|, a primitive type for natural numbers.
\item Only in \salt{}:
|Set| to create set types, with one argument
\end{itemize}

To formalize the type formation rules,
one first needs to describe
what type contexts look like.

\AxiomC{|isContext emptycontext|}
\DisplayProof
\AxiomC{|isContext Gamma|}
\UnaryInfC{|isContext (Gamma, alpha)|}
\DisplayProof
\AxiomC{|isContext (Gamma, alpha)|}
\UnaryInfC{|isContext (Gamma, alpha, isData alpha)|}
\DisplayProof
\AxiomC{|isContext Gamma, Gamma ||- isType tau|}
\UnaryInfC{|isContext (Gamma, x :: tau)|}
\DisplayProof

These are the allowed contexts in what follows.
Let us now look at well-formed types.

\AxiomC{|Gamma,alpha ||- isType alpha|}
\DisplayProof
\AxiomC{|vec (Gamma ||- isType tau_l)|}
\UnaryInfC{|Gamma ||- isType (A (vec tau_l))|}
\DisplayProof
for an ADT |A| with |l| parameters
\AxiomC{|Gamma ||- isType tau|}
\AxiomC{|Gamma ||- isType tau'|}
\BinaryInfC{|Gamma ||- isType (tau -> tau')|}
\DisplayProof
\AxiomC{|Gamma ||- isType Nat|}
\DisplayProof
\AxiomC{|Gamma ||- isType tau|}
\UnaryInfC{|Gamma ||- isType (Set tau)|}
\DisplayProof
in \salt{}.

An algebraic data type is defined like it is in Haskell.
It has a name |A|,
is parameterized by zero or more type variables |vec alpha_l|,
has one or more constructors |C_m|,
each of which is specified by its name and its argument types |vec tau_mn|.
> data A (vec alpha_l) = vec (C_m (vec tau_mn))
As stated above, without the horizontal bars as an abbreviation,
it would look like this.
> data A alpha_1 .. alpha_l = C_1 tau_11 .. tau_1n | .. | C_m tau_m1 .. tau_mn

The only type variables allowed in the types |vec tau_mn| are |vec alpha_l|.
Higher-kinded type variables are not allowed,
which means that a type variable cannot be applied to other types.
This means that something like
> data Apply f a = Apply (f a)
is invalid in \cumin{} and \salt{}
although it is fine in Haskell.

Logic variables in \cumin{} and \salt{} cannot have any type;
only so called |Data| types are allowed.
This is because values of logic variables have to be able to be enumerated.
In contrast, values of function types cannot in general be enumerated
since there may be uncountably many, e.g. |Nat -> Bool|.
Most algebraic data  types, however, are enumerable,
for instance |Bool|, |Nat|,
|List tau| or |Tree tau| for any enumerable |tau|.
To formalize this,
we introduce another judgement |dataIdx A I|
for an ADT |A| with |l| type parameters.
It states that |A (vec tau_l)| is a |Data| type
if |tau_i| is, for each $i \in I$.
Essentially, an ADT is a |Data| type
if the types of all constructors are |Data| types.
The following rules capture this notion.

\AxiomC{|Gamma, alpha, isData alpha ||- isData alpha|}
\DisplayProof
\AxiomC{|Gamma, alpha, dataIdx A I ||- dataIdx A I|}
\DisplayProof
\AxiomC{|Gamma ||- isData Nat|}
\DisplayProof \\
\AxiomC{|Gamma ||- dataIdx A I|}
\AxiomC{$(|vec (Gamma ||- isData tau_i)|)_{i \in I}$}
\BinaryInfC{|Gamma ||- isData (A (vec tau_l))|}
\DisplayProof \\
\AxiomC{$\left(|(vec (Gamma, dataIdx A I, ((vec alpha_l))<:l `elem` I:>, ((vec (isData alpha_l)))<:l `elem` I:> ||- isData tau_mn)|\right)_{mn_m}$}
\UnaryInfC{|Gamma ||- dataIdx A I|}
\DisplayProof
where |data A (vec alpha_l) = vec (C_m (vec tau_mn))|

Let us take a look at some examples.
The deduction of |isData Bool| is quite simple.
\begin{prooftree}
\AxiomC{|Gamma ||- dataIdx Bool emptyset|}
\UnaryInfC{|Gamma ||- isData Bool|}
\end{prooftree}
One can also deduce |dataIdx List (set 1)|. (using the abbreviation |Gamma' := Gamma, dataIdx List (set 1), a, isData a|)
\begin{prooftree}
  \AxiomC{|Gamma' ||- isData a|}
    \AxiomC{|Gamma' ||- dataIdx List (set 1)|}
    \AxiomC{|Gamma' ||- isData a|}
  \BinaryInfC{|Gamma' ||- isData (List a)|}
\BinaryInfC{|Gamma ||- dataIdx List (set 1)|}
\end{prooftree}
Putting things together, |isData (List Bool)| holds, too.
\begin{prooftree}
  \AxiomC{|Gamma ||- dataIdx List (set 1)|}
  \AxiomC{|Gamma ||- isData Bool|}
\BinaryInfC{|Gamma ||- isData (List Bool)|}
\end{prooftree}

As another example, consider the phantom type
> data Phantom a = P
where the type parameter |a| only occurs on the left-hand side.
|Phantom tau| is a |Data| type for any |tau| since its only value is |P|.
So, even for function types like |Nat -> Nat|,
we have |isData (Phantom (Nat -> Nat))|.
\begin{prooftree}
\AxiomC{|Gamma ||- dataIdx Phantom emptyset|}
\UnaryInfC{|Gamma ||- isData (Phantom tau)|}
\end{prooftree}

\section{\cumin{} syntax and typing}

\cumin{} programs consist of algebraic data type declarations
and function definitions.
A function |f| is defined by giving its type signature, an argument list
and the expression it computes, depending on the arguments.
> f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_n = e
The type signature consists type variables to allow polymorphism,
a type class context which specifies
that certain type variables have to be instantiated to |Data| types,
and finally the actual function type.

\cumin{} expressions are of the following form.
> e ::=  x | n | f<:vec tau_m:> | C<:vec tau_m:>
>        | e_1 e_2 | e_1 + e_2 | e_1 == e_2 | failed<:tau:>
>        | let x = e_1 in e_2 | let x :: tau free in e
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) }
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) x -> e' }
> n ::= 0 | 1 | ..
As might be expected, there are variables and literals for natural numbers.
Polymorphic functions and constructors
have to be given type instantiations at the call site.
In principle, these could be inferred automatically
but this complicates type checking.
For the sake of simplicity, we refrained from it.
Function application is written by juxtaposition.
The supported primitive operations are addition for natural numbers
and equality checks for |Data| types, in particular natural numbers.
|failed| signifies that the computation does not yield a result.
It can be used to cut off unwanted computation branches.
Let bindings allow
using the result of a computation more than once in an expression.
Recursive let bindings are not allowed, \ie |x| must not occur in |e_1|.
The construct |let .. free| introduces logic variables,
it is the only logic feature in the language.
Case expressions examine the \emph{scrutinee} |e|
and it is matched with one or more constructor patterns |C_i x_i_j|.
The constructors |C_i| that are matched on must be pairwise different.
There may or may not be a catch-all variable pattern |x| at the end.
It only matches if none of the constructors before did.

\todo[inline]{Describe syntactic sugar.}
\todo[inline]{Describe plain text syntax and indentation.}

There are some definitions that are so common
that we decided to put them in a so-called \emph{prelude},
which is copied to the top of every program.
It defines common data types like lists and boolean types
and functions that handle them.
To be precise, the prelude contains the following declarations.

> data Pair a b = Pair a b
> data List a = Nil | Cons a (List a)
> data Maybe a = Nothing | Just a
> data Either a b = Left a | Right b
> data Bool = False | True
>
> and :: Bool -> Bool -> Bool
> choose :: forall a. a -> a -> a
> const :: forall a b. a -> b -> a
> either :: forall a b c. (a -> c) -> (b -> c) -> Either a b -> c
> filter :: forall a. (a -> Bool) -> List a -> List a
> flip :: forall a b c. (a -> b -> c) -> b -> a -> c
> foldr :: forall a b. (a -> b -> b) -> b -> List a -> b
> fst :: forall a b. Pair a b -> a
> id :: forall a. a -> a
> length :: forall a. List a -> Nat
> map :: forall a b. (a -> b) -> List a -> List b
> maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
> not :: Bool -> Bool
> or :: Bool -> Bool -> Bool
> snd :: forall a b. Pair a b -> b

Furthermore, expressions have to be well-typed.
For example, the term |True + 1| does not make sense,
because the primitive operator |+| only accepts numbers as arguments.
The typing rules are given below.

\begin{gather*}
\AxiomC{|Gamma, x :: tau ||- x :: tau|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- n :: Nat|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- failed<:tau:> :: tau|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- e_1 :: tau' -> tau|}
\AxiomC{|Gamma ||- e_2 :: tau'|}
\BinaryInfC{|Gamma || e_1 e_2 :: tau|}
\DisplayProof
\\[1em]
\AxiomC{|vec (Gamma ||- isData tau_i_j)|}
\UnaryInfC{|Gamma ||- f<:vec tau_m:> :: tau[tau_m/alpha_m]|}
\DisplayProof
\quad\text{where |f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau|}
\\[1em]
\AxiomC{|Gamma ||- C<:vec rho_m:> :: (tau_1 -> .. tau_n -> A (vec alpha_m))[vec (rho_m/alpha_m)]|}
\DisplayProof
\text{for every |data A (vec alpha_m) = .. || C tau_1 .. tau_n || ..|}
\\[1em]
\AxiomC{|Gamma ||- e_1 :: tau'|}
\AxiomC{|Gamma, x :: tau' ||- e_2 :: tau|}
\BinaryInfC{|Gamma ||- let x = e_1 in e_2 :: tau|}
\DisplayProof
\quad
\AxiomC{|Gamma, x :: tau' ||- e :: tau|}
\AxiomC{|Gamma ||- isData tau'|}
\BinaryInfC{|Gamma ||- let x :: tau' free in e :: tau|}
\DisplayProof
\\[1em]
\AxiomC{|Gamma ||- e_1 :: Nat|}
\AxiomC{|Gamma ||- e_2 :: Nat|}
\BinaryInfC{|Gamma ||- e_1 + e_2 :: Nat|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- e_1 :: tau|}
\AxiomC{|Gamma ||- e_2 :: tau|}
\AxiomC{|Gamma ||- isData tau|}
\TrinaryInfC{|Gamma ||- e_1 == e_2 :: Bool|}
\DisplayProof
\\[1em]
\AxiomC{|Gamma ||- e :: A (vec rho_m)|}
\AxiomC{|vec (Gamma, vec (x_i_j :: tau_i_j[vec (rho_m/alpha_m)]) ||- e_i :: tau|}
\BinaryInfC{|Gamma ||- case e of { vec(C_i (vec x_i_j) -> e_i;) } :: tau|}
\DisplayProof
\quad\text{for every |data A (vec rho_m) = vec (C_i (vec tau_i_j))|}
\\[1em]
\AxiomC{\text{\dots (as above)}}
\AxiomC{|Gamma, x :: A (vec rho_m) ||- e' :: tau|}
\BinaryInfC{|Gamma ||- case e of { vec(C_i (vec x_i_j) -> e_i;) x -> e'; } :: tau|}
\DisplayProof
\quad\text{for every |data A (vec rho_m) = vec (C_i (vec tau_i_j))|}
\end{gather*}

In order to type check functions, recall the shape of their definitions.
> f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_n = e
Such a \cumin{} function |f| is well-typed
if the following holds.
\[
\AxiomC{|vec alpha_m, vec (isData alpha_i_j), vec (x_n :: tau_n) ||- e :: tau|}
\DisplayProof
\]
A \cumin{} program is well-typed if each of its functions is well-typed.

\subsection{Examples}

As an example, consider the following program.
> choose :: forall a. a -> a -> a
> choose x y = let c :: Bool free in case c of { True -> x; False -> y }
>
> map :: forall a b. (a -> b) -> List a -> List b
> map f xs = case xs of { Nil -> Nil<:b:>; Cons y ys -> Cons<:b:> (f<:a:> y) (map<:a,b:> f<:a:> ys) }

To prove that |choose| is well-typed,
consider the following deduction.
Let |Gamma := a, x :: a, y :: a|.
\begin{prooftree}
    \AxiomC{|Gamma, c :: Bool ||- c :: Bool|}
    \AxiomC{|Gamma, c :: Bool ||- x :: a|}
    \AxiomC{|Gamma, c :: Bool ||- y :: a|}
  \TrinaryInfC{|Gamma, c :: Bool ||- case c of { True -> x; False -> y } :: a|}
    \AxiomC{\dots}
  \UnaryInfC{|Gamma ||- isData Bool|}
\BinaryInfC{|Gamma ||- let c :: Bool free in case c of { True -> x; False -> y } :: a|}
\end{prooftree}
The judgment |Gamma ||- isData Bool| has been proven before.
Similarly, one can prove that |map| is well-typed.
Let |Gamma := f :: a -> b, xs :: List a| and |Gamma' := Gamma, y :: a, ys :: List a|.
\begin{prooftree}
\small
  \AxiomC{|Gamma ||- xs :: List a|}
  \AxiomC{|Gamma ||- Nil<:b:> :: List b|}
      \AxiomC{\dots}
    \UnaryInfC{|Gamma' ||- Cons<:b:> .. :: List b -> List b|}
      \AxiomC{\dots}
    \UnaryInfC{|Gamma' ||- map<:a,b:> .. :: List b|}
  \BinaryInfC{|Gamma, y :: a, ys :: List a ||- Cons<:b:> (f y) (map<:a,b:> f ys) :: List b|}
\TrinaryInfC{|Gamma ||- case xs of { Nil -> Nil<:b:>; Cons y ys -> Cons<:b:> (f y) (map<:a,b:> f ys) } :: List b|}
\end{prooftree}
The missing subderivations look like this.
\begin{prooftree}
  \AxiomC{|Gamma' ||- Cons<:b:> :: b -> List b -> List b|}
    \AxiomC{|Gamma' ||- f :: a -> b|}
    \AxiomC{|Gamma' ||- y :: a|}
  \BinaryInfC{|Gamma' ||- (f y) :: b|}
\BinaryInfC{|Gamma' ||- Cons<:b:> (f y) :: List b -> List b|}
\end{prooftree}
\begin{prooftree}
    \AxiomC{|Gamma' ||- map<:a,b:> :: (a -> b) -> List a -> List b|}
    \AxiomC{|Gamma' ||- f :: List a|}
  \BinaryInfC{|Gamma' ||- map<:a,b:> f :: List a -> List b|}
  \AxiomC{|Gamma' ||- ys :: List a|}
\BinaryInfC{|Gamma' ||- map<:a,b:> f ys :: List b|}
\end{prooftree}

\section{\salt{} syntax and typing}

\section{Implementation}
