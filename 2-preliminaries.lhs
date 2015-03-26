\chapter{Preliminaries}

In this chapter,
I will give a more precise description of \cumin{} and \salt{},
as well as some remarks on the implementation of parsers and type checkers.
This part of the implementation was done together with Fabian Thorand,
who wrote his bachelor thesis,
which is concerned with other aspects of \cumin{} and \salt{},
over the same period of time.

\section{Notation and Conventions}

In the following,
a sequence of objects |z_1 .. z_n| will be denoted |vec z_n|.
An empty sequence, \ie $n = 0$, is allowed.
If the index is unclear,
it is written |((vec z_n))<:n:>!|,
or even $|((vec z_n))|_{n \in S}$
where $S$ denotes the range of $n$.
The notation |e[y/x]| means
replacing every unbound occurrence of |x| in |e| with |y|.
By convention,
|alpha, beta| denote type variables;
|rho, tau| denote types;
|x,y| denote variables;
|m,n| denote natural numbers;
|p| denotes a pattern in pattern matches;
|e| denotes an expression;
|f| denotes a function;
|C| denotes a constructor;
|A| denotes an algebraic data type;
and |Gamma| denotes a context,
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
denoted~|Gamma|.
The judgment is then written with the turnstile symbol:
$\Gamma \vdash \text{judgment}$.
More details on the presentation of type systems
can be found in \cite{typing-systems}.

\section{Types in \cumin{} and \salt{}}

Types can either be a type variable
or a type constructor applied to zero or more types,
whose number must match the arity of the type constructor.
The following list contains all valid type constructors.
\begin{itemize}
\item The name of an algebraic data type. Its arity is the number of type parameters in the definition.
\item The function type constructor |->|, with two arguments.
It associates to the right.
\item |Nat|, a primitive type for natural numbers.
\item Only in \salt{}:
|Set| to create set types, with one argument.
\end{itemize}

To make this exact,
one first needs to describe
what valid type contexts look like (\cref{contexts}).
These are the allowed contexts in typing judgments.
The above description of types can then be
formalized and is shown in \cref{types}.

Typing judgments are always made with respect to a given program $P$.
After all, they can depend on the ADTs defined in $P$ and,
as we will see later,
on the function definitions in $P$, too.
Because of that, we would theoretically have to index all typing judgments
by that program.
However, we omit the index for the sake of readability.

\begin{figure}[t]
\begin{gather*}
\AxiomC{|isContext emptycontext|}
\DisplayProof
\quad
\AxiomC{|isContext Gamma|}
\UnaryInfC{|isContext (Gamma, alpha)|}
\DisplayProof
\quad
\AxiomC{|isContext Gamma|}
\AxiomC{|Gamma ||- isType tau|}
\BinaryInfC{|isContext (Gamma, x :: tau)|}
\DisplayProof
\\[1em]
\AxiomC{|isContext (Gamma, alpha)|}
\UnaryInfC{|isContext (Gamma, alpha, isData alpha)|}
\DisplayProof
\quad
\AxiomC{|isContext Gamma|}
\AxiomC{$I \subset \mathbb{N}$}
\BinaryInfC{|isContext (Gamma, dataIdx A I)|}
\DisplayProof
\quad\text{for an ADT |A|}
\end{gather*}
\caption{Context formation rules}
\label{contexts}
\hrulefill
\end{figure}

\begin{figure}[t]
\begin{gather*}
\AxiomC{|Gamma,alpha ||- isType alpha|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- isType Nat|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- isType tau|}
\AxiomC{|Gamma ||- isType tau'|}
\BinaryInfC{|Gamma ||- isType (tau -> tau')|}
\DisplayProof
\\[1em]
\AxiomC{|vec (Gamma ||- isType tau_l)|}
\UnaryInfC{|Gamma ||- isType (A (vec tau_l))|}
\DisplayProof
\quad\text{for an ADT |A| with |l| parameters}
\qquad
\AxiomC{|Gamma ||- isType tau|}
\UnaryInfC{|Gamma ||- isType (Set tau)|}
\DisplayProof
\quad\text{in \salt{}}
\end{gather*}
\caption{Type formation rules}
\label{types}
\hrulefill
\end{figure}

While there are only three built-in algebraic data types in \cite{orig},
namely lists, pairs and booleans,
we considered this to be too limiting
and decided to augment the languages with general ADTs.
Such an algebraic data type is defined like it is in Haskell.
It has a name |A|,
is parameterized by zero or more type variables |vec alpha_l|,
has one or more constructors |vec C_m|,
each of which is specified by its name and its argument types |vec tau_mn|.
> data A alpha_1 .. alpha_l = C_1 tau_11 .. tau_1n | .. | C_m tau_m1 .. tau_mn
According to the above conventions,
I will often abbreviate it like this:
> data A (vec alpha_l) = vec (C_m (vec tau_mn))

The only type variables allowed in the types |vec tau_mn| are |vec alpha_l|.
Higher-kinded type variables are not supported,
which means that a type variable cannot be applied to other types.
As a consequence, the following data type is invalid in \cumin{} and \salt{}
although it is permitted in Haskell.
> data D f a = D (f a)

Logic variables in \cumin{} and the |unknown| primitive in \salt{}
cannot have an arbitrary type;
only so called |Data| types are permitted.
This is because values of logic variables have to be enumerable.
As a counterexample, values of function types
do not have a natural structure for enumeration.
Most algebraic data  types, however, are structurally enumerable,
for instance |Bool|, |Nat|,
|List tau| or |Tree tau| for any enumerable |tau|.
They can be enumerated because all constructors can be listed
and their arguments are enumerable.

In order to formalize this notion,
we introduce another judgment |dataIdx A I|
for an ADT |A| with |l| type parameters
where |I| has to be a subset of $\{1,\dots,l\}$.
It states that |A (vec tau_l)| is a |Data| type
if, for each $i \in I$, |tau_i| is a |Data| type.
Essentially, an ADT is a |Data| type
if the types of the arguments of all constructors are |Data| types.
The rules in \cref{data-types} capture this notion.
Note that this is another deviation from \cite{orig},
which only specifies simple rules for the three built-in ADTs.
As we allow general algebraic data types,
these more intricate rules are necessary.

\begin{figure}[t]
\begin{gather*}
\AxiomC{|Gamma, alpha, isData alpha ||- isData alpha|}
\DisplayProof
\quad
\AxiomC{|Gamma, alpha, dataIdx A I ||- dataIdx A I|}
\DisplayProof
\\[1em]
\AxiomC{|Gamma ||- isData Nat|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- dataIdx A I|}
\AxiomC{$(|vec (Gamma ||- isData tau_i)|)_{i \in I}$}
\BinaryInfC{|Gamma ||- isData (A (vec tau_l))|}
\DisplayProof
\\[1em]
\AxiomC{$\left(|(vec (Gamma, dataIdx A I, (vec alpha_l), ((vec (isData alpha_l)))<:l `elem` I:> ||- isData tau_mn)|\right)_{mn_m}$}
\UnaryInfC{|Gamma ||- dataIdx A I|}
\DisplayProof
\quad\text{where |data A (vec alpha_l) = vec (C_m (vec tau_mn))|}
\end{gather*}
\caption{Rules for |Data| types}
\label{data-types}
\hrulefill
\end{figure}

Let us take a look at some examples.
As all constructors of |Bool| are nullary,
the deduction of |isData Bool| is quite simple.
\begin{prooftree}
\AxiomC{|Gamma ||- dataIdx Bool emptyset|}
\UnaryInfC{|Gamma ||- isData Bool|}
\end{prooftree}
One can also deduce |dataIdx List (set 1)|,
using the abbreviation |Gamma' := Gamma, dataIdx List (set 1), a, isData a|.
\begin{prooftree}
  \AxiomC{|Gamma' ||- isData a|}
    \AxiomC{|Gamma' ||- dataIdx List (set 1)|}
    \AxiomC{|Gamma' ||- isData a|}
  \BinaryInfC{|Gamma' ||- isData (List a)|}
\BinaryInfC{|Gamma ||- dataIdx List (set 1)|}
\end{prooftree}
Putting these two results together,
we can show that |isData (List Bool)| holds, too.
\begin{prooftree}
  \AxiomC{|Gamma ||- dataIdx List (set 1)|}
  \AxiomC{|Gamma ||- isData Bool|}
\BinaryInfC{|Gamma ||- isData (List Bool)|}
\end{prooftree}

If a type variable is used in no constructor,
it does not have to be a |Data| type.
As an example, consider the phantom type
> data Phantom a = Phantom
where the type parameter |a| only occurs on the left-hand side.
|Phantom tau| is a |Data| type for any |tau| since its only value is |Phantom|.
So, even for function types like |Nat -> Nat|,
we have |isData (Phantom (Nat -> Nat))|.
\begin{prooftree}
\AxiomC{|Gamma ||- dataIdx Phantom emptyset|}
\UnaryInfC{|Gamma ||- isData (Phantom tau)|}
\end{prooftree}

\section{\cumin{} Syntax and Typing}

\subsection{Syntax}

\cumin{} programs consist of algebraic data type declarations
and function definitions.
A function |f| is defined by giving its \emph{type signature},
a list of variables that constitute the arguments,
and the expression it computes, depending on the arguments.
> f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_n = e
The type signature consists of \emph{type variables} to allow polymorphism,
a \emph{type class context} which specifies
that certain type variables have to be instantiated to |Data| types,
and finally the actual function type.
One does not need to write the empty context |() =>|
if the function has no |Data| constraints,
and if there are no type variables,
the $\forall.$ may be dropped, as well.

The shape of \cumin{} expressions is shown in \cref{cumin-exp}.
\begin{figure}[t]
> e ::=  x | n | f<:vec tau_m:> | C<:vec tau_m:>
>        | e_1 e_2 | e_1 + e_2 | e_1 == e_2 | failed<:tau:>
>        | let x = e_1 in e_2 | let x :: tau free in e
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) }
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) x -> e' }
> n ::= 0 | 1 | ..
\caption{Syntax of \cumin{} expressions}
\label{cumin-exp}
\hrulefill
\end{figure}
As might be expected,
the syntax includes variables and literals for natural numbers.
Polymorphic functions and constructors
have to be given type instantiations at the call site,
denoted by subscripts.
In principle, these could be inferred automatically,
but this complicates type checking.
For the sake of simplicity, these annotations are mandatory.
Function application is written by juxtaposition,
it associates to the left and has the highest binding precedence.
The supported primitive operations are addition for natural numbers
and equality checks for |Data| types, in particular natural numbers.
Comparison for equality requires a certain structure on the values,
thus the |Data| requirement.
After all, checking whether two functions are equal is undecidable in general.
As usual, the operator |+| binds more tightly than |==|.
The former associates to the left and the latter is not associative.
Parentheses can be used for structuring expressions.
The keyword |failed| signifies that the computation does not yield a result.
It can be used to \enquote{cut off} unwanted computation branches.
Let bindings allow
using the result of a computation more than once in an expression
by binding it to a variable |x|.
Recursive let bindings are not allowed, \ie |x| must not occur in |e_1|.
The construct |let .. free| introduces logic variables;
it is the only logic feature in the language.
Case expressions examine the value of an expression,
called the \emph{scrutinee}.
Its value is matched with the constructor patterns |C_i x_i_j|.
The constructors |C_i| that are matched on must be pairwise different
and there must be at least one constructor pattern.
There may or may not be a catch-all variable pattern |x| at the end.
It only matches if none of the constructors before did.

We modified the \cumin{} syntax from \cite{orig} in the following points.
It was already mentioned that we allow general ADTs.
As a consequence,
the syntax for constructors and case expressions has to be generalized as well.
Additionally, we lift the requirement
that constructors have to be fully applied.
Moreover, the type class context in function signatures
is written differently.
In the original paper, the type variables with a |Data| requirement
where indicated by tagging the quantifier $\forall$ with a |*|.
Another discrepancy are case expressions.
While the original syntax expects one pattern for each constructor,
we permit a catch-all variable pattern at the end
and do not require every constructor to be matched.
Furthermore, the primitive $\textbf{\text{anything}}$|<:tau:>!| from \cite{orig}
(corresponding to |let x :: tau free in x|)
is removed in favor of the |let .. free| construct.
Finally, the keyword $\textbf{\text{failure}}$ is renamed to |failed|.

Besides the mathematical notation,
there is also a plain-text representation of \cumin{} code.
The straightforward correspondence is shown in \cref{cumin-plain}.
\begin{figure}[t]
\centering
\begin{tabular}{l l}
  Mathematical notation & Plain text \\
  \hline
  |forall a.| & \texttt{forall a.} \\
  |->| & \texttt{->} \\
  |=>| & \texttt{=>} \\
  |f<:t:>| & \texttt{f<:t:>} \\
  |==| & \texttt{==} \\
\end{tabular}
\caption{Plain text representation of \cumin{}}
\label{cumin-plain}
\hrulefill
\end{figure}
As in Haskell, code can also be written using indentation
instead of braces and semicolons:
> case e of
>   C_1 .. -> ..
>   C_2 .. -> ..

There are some data types and functions that are so common and useful
that we decided to put them in a so-called \emph{prelude},
which is copied to the top of every program.
It defines data types like lists and booleans,
as well as functions that operate on them.
The types of the definitions of the prelude are listed in \cref{cumin-prelude}.

\begin{figure}[t]
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
> guard :: forall a. Bool -> a -> a
> id :: forall a. a -> a
> length :: forall a. List a -> Nat
> map :: forall a b. (a -> b) -> List a -> List b
> maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
> not :: Bool -> Bool
> or :: Bool -> Bool -> Bool
> snd :: forall a b. Pair a b -> b
\caption{The \cumin{} Prelude}
\label{cumin-prelude}
\hrulefill
\end{figure}

Finally, there is some syntactic sugar
to make programs easier to read and write.
List literals can be written in the natural way |[e_1, .., e_n]<:tau:>!|,
which is desugared to the expression
|Cons<:tau:> e_1 (.. (Cons<:tau:> e_n Nil<:tau:>) ..)|.

\subsection{Typing}

\cumin{} expressions have to be well-typed.
For example, the term |True + 1| does not make sense,
because the primitive operator |+| only accepts natural numbers as arguments.
The typing rules are given in \cref{cumin-typing}.
They are based on \cite{orig}
but take our modifications and generalizations of the language into account.
Another deviation from the original paper,
which is does not affect the syntax, can be seen, as well.
While the original paper restricts equality checks to natural numbers,
we allow all |Data| types.
\begin{figure}[t]
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
\BinaryInfC{|Gamma ||- e_1 e_2 :: tau|}
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
\quad\text{for every |data A (vec alpha_m) = vec (C_k (vec tau_k_j))|}
\\[1em]
\AxiomC{\text{\dots (as above)}}
\AxiomC{|Gamma, x :: A (vec rho_m) ||- e' :: tau|}
\BinaryInfC{|Gamma ||- case e of { vec(C_i (vec x_i_j) -> e_i;) x -> e'; } :: tau|}
\DisplayProof
\quad\text{for every |data A (vec alpha_m) = vec (C_k (vec tau_k_j))|}
\end{gather*}
\caption{Typing rules for \cumin{} expressions}
\label{cumin-typing}
\hrulefill
\end{figure}
In order to type check functions, recall the shape of their definitions.
> f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_n = e
Such a \cumin{} function |f| is well-typed
if the following judgment holds.
\[
\AxiomC{|vec alpha_m, vec (isData alpha_i_j), vec (x_n :: tau_n) ||- e :: tau|}
\DisplayProof
\]
A \cumin{} program is well-typed if each of its ADTs and functions is well-typed.

\subsection{Examples}

As an example, consider the following program.
> choose :: forall a. a -> a -> a
> choose x y = let c :: Bool free in case c of
>   True -> x
>   False -> y
>
> map :: forall a b. (a -> b) -> List a -> List b
> map f xs = case xs of
>   Nil        -> Nil<:b:>
>   Cons y ys  -> Cons<:b:> (f y) (map<:a,b:> f ys)

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
Similarly, one can derive that |map| is well-typed.
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

\section{\salt{} Syntax and Typing}
\label{sec:salt}

The syntax of \salt{} is quite similar to \cumin{} (\cref{salt-exp}).
However, it replaces the |let .. free| construct
with the keyword |unknown<:tau:>!|,
which represents the set of values of the |Data| type |tau|.
As mentioned in the introduction,
other primitives for sets are
|set| for creating singleton sets
and |>>=| for indexed unions.
This operator binds least tightly and associates to the left.
\begin{figure}[t]
> e ::=  x | n | f<:vec tau_m:> | C<:vec tau_m:> | \x :: tau -> e
>        | e_1 e_2 | e_1 + e_2 | e_1 == e_2 | failed<:tau:>
>        | unknown<:tau:> | set e | e_1 >>= e_2
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) }
>        | case e of { vec(C_i (vec x_i_j) -> e_i;) x -> e' }
> n ::= 0 | 1 | ..
\caption{Syntax of \salt{} expressions}
\label{salt-exp}
\hrulefill
\end{figure}
As \salt{} has explicit lambda abstractions,
there is no need for function arguments.
Hence, function definitions are simpler than in \cumin{}.
> f :: forall (vec alpha_m). ((vec (Data alpha_i_j))) => tau
> f = e

The \salt{} syntax deviates slightly from \cite{orig}, as well.
Except for the |let .. free| construct,
the modifications of \cumin{} also apply to \salt{}.
Additionally, the $\textbf{\text{anything}}$ primitive from the original paper
is renamed to |unknown|.
Furthermore, the syntax for indexed unions is different.
The original paper writes $|e_1| \ni |x| \bigcup |e_2|$
for what we denote by |e_1 >>= \x :: tau -> e_2|.
Our syntax is more liberal
because we do not restrict ourselves to lambda abstractions
on the right-hand side.

\salt{} has the same plain text representation as \cumin{}.
The additional symbols are written as shown in \cref{salt-plain}.
Since \verb!Set! is a reserved type constructor,
it cannot be the name of an ADT.

\begin{figure}[t]
\centering
\begin{tabular}{l l}
Mathematical notation & plain text \\
\hline
|Set t| in types & \verb!Set t! \\
|set e| in expressions & \verb!{e}! \\
|\| & \verb!\! \\
|>>=| & \verb!>>=!
\end{tabular}
\caption{Plain text representation of \salt{} syntax}
\label{salt-plain}
\hrulefill
\end{figure}

As for \cumin{}, we created a \salt{} prelude with useful definitions.
It is mainly a manual translation of the \cumin{} prelude.
There are only two major differences.
> choose :: forall a. Set a -> Set a -> Set a
> sMap :: forall a b. (a -> b) -> Set a -> Set b
The \salt{} version of |choose| operates on sets
by forming their union.
There is also a new function |sMap|
which acts on sets like |map| acts on lists.
It yields a set where the given function has been applied
to every element of the original one.

There is also an alternative prelude that is generated
by the translation method described in chapter 4.
It behaves the same but due to the nature of the translation,
its functions contain more sets than necessary, for example,
|id| is translated to |id :: forall a. Set (a -> Set a)|.

The \salt{} typing rules are similar to those of \cumin{}.
The ones for let bindings are now unnecessary.
Instead, there are rules for lambda abstractions,
and most importantly, for handling sets (\cref{salt-typing}).
\begin{figure}[t]
\begin{gather*}
\AxiomC{|Gamma, x :: tau' ||- e :: tau|}
\UnaryInfC{|Gamma ||- (\x :: tau' -> e) :: tau' -> tau|}
\DisplayProof
\\[1em]
\AxiomC{|Gamma ||- isData tau|}
\UnaryInfC{|Gamma ||- unknown<:tau:> :: Set tau|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- e :: tau|}
\UnaryInfC{|Gamma ||- set e :: Set tau|}
\DisplayProof
\quad
\AxiomC{|Gamma ||- e_1 :: Set tau|}
\AxiomC{|Gamma ||- e_2 :: tau -> Set tau'|}
\BinaryInfC{|Gamma ||- e_1 >>= e_2 :: Set tau'|}
\DisplayProof
\end{gather*}
\caption{\salt{}-specific typing rules}
\label{salt-typing}
\hrulefill
\end{figure}
A function in the shape given above is well-typed
if the following judgment is correct.
\[
\AxiomC{|vec alpha_m, vec (isData alpha_i_j) ||- e :: tau|}
\DisplayProof
\]

Having specified the \salt{} syntax and typing rules,
let us take a look at some examples.
It is instructive to translate the above \cumin{} programs to \salt{}.
> choose :: forall a. Set a -> Set a -> Set a
> choose = \x :: Set a -> \y :: Set a -> unknown<:Bool:> >>= \c :: Bool ->
>   case c of 
>     True -> x
>     False -> y

> map :: forall a b. (a -> b) -> List a -> List b
> map = \f :: (a -> b) -> \xs :: List a -> case xs of
>   Nil        -> Nil<:b:>
>   Cons y ys  -> Cons<:b:> (f y) (map<:a,b:> f ys)
Proving that |choose| is well-typed works similarly as above.
Let |Gamma := a, x :: Set a, y :: Set a| and |Gamma' := Gamma, c :: Bool|.
\begin{prooftree}
      \AxiomC{|..|}
    \UnaryInfC{|Gamma ||- isData Bool|}
  \UnaryInfC{|Gamma ||- unknown<:Bool:> :: Set Bool|}
      \AxiomC{|Gamma' ||- c :: Bool|}
      \AxiomC{|Gamma' ||- x :: Set a|}
      \AxiomC{|Gamma' ||- y :: Set a|}
    \TrinaryInfC{|Gamma' ||- case c of { True -> x; False -> y } :: Set a|}
  \UnaryInfC{|Gamma ||- \c :: Bool -> case c of { .. } :: Bool -> Set a|}
\BinaryInfC{|Gamma ||- unknown<:Bool:> >>= \c :: Bool -> case c of { .. } :: Set a|}
\UnaryInfC{|a, x :: Set a ||- \y :: Set a -> unknown<:Bool:> >>= \c :: Bool -> case c of { .. } :: Set a -> Set a|}
\UnaryInfC{|a ||- \x :: Set a -> \y :: Set a -> unknown<:Bool:> >>= \c :: Bool -> case c of { .. } :: Set a -> Set a -> Set a|}
\end{prooftree}

The proof of well-typedness of |map| very similar to the one in \cumin{},
so it can be safely left out.
Instead let us understand the function |sMap|.
> sMap :: forall a b. (a -> b) -> Set a -> Set b
> sMap = \f :: (a -> b) -> \xs :: Set a -> xs >>= \x :: a -> set (f x)
This function applies |f| to every element of |xs|.
As the only combinator for sets is the indexed union with |>>=|,
|sMap| constructs the singleton set |set (f x)|
for every element |x| of |xs| and forms the union of these sets,
yielding the set $\{ |(f x)| || |x| \in |xs| \}$, as desired.
The relevant expression |xs >>= \x :: a -> set (f x)|
is perhaps more suggestive when written in the notation of \cite{orig},
namely as $|xs| \ni |x| \bigcup |set (f x)|$.
To check type correctness, let |Gamma := a, b, f :: a -> b, xs :: Set a|.
\begin{prooftree}
  \AxiomC{|Gamma ||- xs :: Set a|}
        \AxiomC{|Gamma, x :: a ||- f :: a -> b|}
        \AxiomC{|Gamma, x :: a ||- x :: a|}
      \BinaryInfC{|Gamma, x :: a ||- f x :: b|}
    \UnaryInfC{|Gamma, x :: a ||- set (f x) :: Set b|}
  \UnaryInfC{|Gamma ||- \x :: a -> set (f x) :: a -> Set b|}
\BinaryInfC{|Gamma ||- xs >>= \x :: a -> set (f x) :: Set b|}
\UnaryInfC{|a, b, f :: (a -> b) ||- \xs :: Set a -> xs >>= \x :: a -> set (f x) :: Set a -> Set b|}
\UnaryInfC{|a, b ||- \f :: (a -> b) -> \xs :: Set a -> xs >>= \x :: a -> set (f x) :: (a -> b) -> Set a -> Set b|}
\end{prooftree}

\section{Implementation}

Before implementing a semantics or translation method involving the two languages,
some groundwork had to be done.
\cumin{} and \salt{} programs have to be parsed
into an \emph{abstract syntax tree (AST)}.
A type checker for these ASTs is needed
and a pretty-printer will be useful as well.
This functionality was implemented together with Fabian Thorand,
whose bachelor thesis is also concerned with \cumin{} and \salt{}.

The functionality is split into three packages:
\texttt{funlogic-common}, \texttt{language-cumin} and \texttt{language-salt}.
The first one contains common functionality for both \cumin{} and \salt{},
like the representation of types.
The other two packages deal with the two languages specifically,
each one providing a parser, pretty-printer and type checker.

All implementations in this thesis were developed in Haskell
using the standard tools,
namely the \emph{Glasgow Haskell Compiler} (GHC)\footnote{
\url{https://www.haskell.org/ghc/}}, version 7.8.3,
and the \emph{cabal} build system\footnote{
\url{https://www.haskell.org/cabal/}}, version 1.18.
The dependencies were installed from \emph{Hackage}.\footnote{
The Haskell package archive, \url{http://hackage.haskell.org/}}
Detailed Installation instructions can be found on the attached CD.

\subsection{Abstract Syntax Tree}
\label{sec:ast}

The objects in \cumin{} and \salt{} are straightforwardly modeled
as algebraic data types in Haskell.
For instance, a type is represented like this.
> data Type = TVar TVName | TCon TyConName [Type]
A type is either a type variable or
a type constructor applied to a list of types.
Hence, |TCon "->" [TVar "a", TCon "Set" [TCon "Bool" []]]|
is the representation of the \salt{} type |a -> Set Bool|.
The representation of expressions is similarly given
by introducing one constructor for each kind of expression
from the previous sections.

One notorious problem in writing compilers
is the representation of bound variables.
In our implementation, they are simply represented by their names.
Generally, this can cause a number of problems with substitution
because free variables may be captured:
Consider the two lambda terms |\x -> y| and |\y -> z|.
Blindly substituting the former term for |z|
yields |\y -> \x -> y|, which is incorrect
as the variable |y| is not free anymore.
For the correct solution |\y' -> \x -> y|, variables have to be renamed.
There are more elaborate representations for capture avoidance,
like the one I explain in \cref{sec:bound},
but we opted against that complexity in the common packages
since the kind of substitution needed for type checking,
namely instantiating type variables on function invocations,
can never lead to unwanted capturing.
That is because type variable bindings are always on the top level,
introduced by $\forall$, and cannot be nested.

\subsection{Parser}

Programs are given in the plain text format specified above.
This textual representation needs to be parsed and converted to an AST.
Instead of writing a parser by hand,
we took the usual approach in the Haskell community
and used a parser combinator library \cite{parser-combinators}.
The most well-known one is \texttt{parsec}
but we chose \texttt{trifecta}\footnote{
\url{http://hackage.haskell.org/package/trifecta}}
by Edward Kmett
because it has more readable and (subjectively) better error messages.
As we wanted indentation-sensitive parsing,
we used the library \texttt{indentation} \cite{indentation},
which builds on top of \texttt{trifecta}.
Parser combinators are a very readable and concise way of defining parsers.
For instance, the parser for lambda abstractions
\verb!\x :: t -> e! in \salt{} looks like this.
(slightly modified for clarity)
> lambdaE  =     ELam
>          <$>  (symbol "\\" *> varIdent)
>          <*>  (symbol "::" *> complexType)
>          <*>  (symbol "->" *> expression)
The combinator |*>| combines two parsers
by running the first one and then the second one,
returning the result of the second one.
In this way, |lambdaE| first parses the bound variable,
then its type, and then the expression.
|ELam| constructs an expression AST from this data.
The combinators |<$>| and |<*>| \enquote{lift} this operation
to an operation on parsers, such that |lambdaE| is itself a parser
that returns an expression.
Parsers for other kinds of expressions look similar.

After having collected all top-level and data type definitions,
they have to be checked for duplicates.
Giving different functions the same name is obviously ambiguous
and such programs have to be rejected.
Similarly, ADT names must be unique among each other
and the same applies to constructor names.

\subsection{Pretty-printer}

Pretty-printing is in a way the opposite of parsing:
It means transforming an AST into human-readable code.
As for parsing, we use a combinator library for pretty-printing,
called \texttt{ansi-wl-pprint}\footnote{
\url{http://hackage.haskell.org/package/ansi-wl-pprint}}.
It is based on \cite{pretty} but with some extensions.
This particular library allows colored output,
which makes syntax highlighting in the terminal possible.
The pretty-printer is aware of operator precedence,
so it only uses parentheses where necessary.
It is used for automatically generated programs, debugging
and in the translation program (see chapter 4).

\subsection{Type Checker}

The type checker is essentially a direct implementation of the typing rules.
It runs as a monadic computation \cite{monads}
to keep track of the type variables
and bound variables that are in scope.\footnote{
Monads can be used to thread a context through a computation,
among other things.
Explaining monads properly is beyond the scope of this thesis, however.}
The syntax tree can simply be checked from the bottom up,
composing the types of smaller expressions to larger ones,
according to the typing rules.
No complicated inference is needed
since the expressions have all the necessary type annotations
to determine their type locally.
(In contrast, a Haskell type inference would have to
take global constraints into account.)
As soon as an inconsistency is found,
a type error is reported.

The only thing that deserves a special remark is the inference of |Data| types.
The inference of the |dataIdx A I| judgments is done once,
at the beginning of type checking, and the result is stored.
Closely following the typing rules
to determine the index set $I$ of type variables
that need to be |Data| types would be inefficient
because we would have to try all possible sets $I$.
Instead, the following fixpoint iteration is used.
We keep track of which ADTs are |Data| types and if so,
which type variables have to be |Data| types for the ADT to be one.
Let $I_{|A|}$ be this set of constraints for an ADT |A|.
It corresponds to the judgment |dataIdx A I|.
In the beginning, every ADT |A| is assumed to be a |Data| type
without any constraints, \ie $I = \emptyset$.
In each iteration, for each ADT |A|, and each constructor |C|,
type variables in the argument type of |C| are added to this set.
For argument types that are type constructors |D| applied to other types,
we first check
that the |D| is a |Data| type,
according to the current knowledge.
If not, |A| itself cannot be a |Data| type.
Otherwise, we require the types to which the |D| is applied
to be |Data| types,
but only those with an index in the constraint set $I_{|D|}$.

In this way, more necessary |Data| constraints are accumulated
until a fixed point is reached.
Then, the constraints are also sufficient.
Such a fixed point is reached
since the syntactic nesting level of data types is bounded.
When the maximum nesting level has been explored,
there are no new constraints to be discovered.
This procedure gives the same result as the formal typing rules
because it requires no more than the necessary |Data| constraints.
To illustrate the method, consider the following definitions.
> data List a = Nil | Cons a (List a)
> data Alt a b = End | Cont a (Alt b a)
The second data type represents a list with alternating types.
How does the fixpoint iteration proceed?
At first, $I_{|List|} = \emptyset$ and $I_{|Alt|} = \emptyset$.
In the first iteration,
the index 1 for the type variable |a|
is added to $I_{|List|}$ and $I_{|Alt|}$
since |a| is a constructor argument type.
The second constructor arguments of |Cons| and |Cont|
do not produce new constraints
since |List| and |Nat| have no |Data| requirements in the beginning, yet.
After the first iteration, we thus have $I_{|List|} = I_{|Alt|} = \{1\}$.
In the second iteration, the |List a| argument of |Cons|
requires |a| to be a |Data| type
because we now have $1 \in I_{|List|}$.
So 1 (the index of |a|) is again added to $I_{|List|}$,
leaving the set unchanged.
Furthermore, the |Alt b a| argument of |Cont|
requires |b| to be a |Data| type, as well,
because $1 \in I_{|Alt|}$
and |b| is used as the first type argument of |Alt|.
As |b| is the second type parameter in the definition of |Alt|,
the index 2 is added to $I_{|Alt|}$.
The result $I_{|List|} = \{1\}, I_{|Alt|} = \{1,2\}$
does not change in the next iteration,
which means that it is the desired fixed point.
