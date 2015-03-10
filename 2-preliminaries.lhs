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

\section{\salt{} syntax and typing}

\section{Implementation}
