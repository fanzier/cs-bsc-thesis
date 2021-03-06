\chapter{Operational Semantics for \cumin{}}

Having defined
what well-formed \cumin{} programs look like,
we want to define their meaning
by giving them a \emph{semantics}.
There are two kinds of semantics,
\emph{denotational} and \emph{operational} ones.
A denotational semantics describes
the meaning of programs
as mathematical objects.
Denotational semantics for \cumin{} and \salt{}
were given in \cite{orig}
and were implemented by Fabian Thorand in his bachelor thesis.

The other approach are operational semantics.
These describe the program's execution directly,
instead of translating it to mathematical objects.
An operational semantics for (a subset of) Curry can be found in \cite{bh},
which is a modification of \cite{ahhov}.
Based on this,
Stefan Mehner describes such a semantics \cite{cuminreport}
for the variant of \cumin{} without general algebraic data types from \cite{orig}.
A few small changes and generalizations lead to the semantics
I describe below.
Before that, I want to point out some properties of \cumin{}
that may seem surprising at first.

\section{Peculiarities of \cumin{}}
\label{sec:pecularities}

To gain a better understanding of nondeterminism in \cumin{},
let us look at some examples of \cumin{} functions.

> coin :: Nat
> coin = choose<:Nat:> 0 1
>
> double :: Nat -> Nat
> double x = x + x
>
> maybeDouble1 :: Nat -> Nat
> maybeDouble1 = choose<:Nat -> Nat:> id<:Nat:> double
>
> maybeDouble2 :: Nat -> Nat
> maybeDouble2 n = maybeDouble1 n

Contrary to what one might expect,
|coin + coin| and |double coin| behave differently.
The first one evaluates to 0, 1 or 2
as each of the summands can yield 0 or 1.
The second expression can only evaluate to 0 or 2.
This is because of an intricacy of \cumin{} (and Curry),
called \emph{call-time choice}.
It means that occurrences of |x| in the body of |double|
always represent the same shared value.
The choice for the desired value of the nondeterministic operation |coin|
is made at call-time.
However, the value itself is still computed lazily (call-by-need).
Call-time choice also affects let-bindings:
|let x = coin in x + x| behaves exactly the same as |double coin|.
In particular, one cannot substitute |coin| for |x| in |x + x|
without changing the meaning.
In contrast, this is fine in purely functional languages like Haskell.

Coming from Haskell,
it will also be surprising that |maybeDouble1| and |maybeDouble2|
are \emph{not} equivalent.
This shows that $\eta$-equivalence
does not generally hold for \cumin{} (and Curry).
The difference between these two functions can only be observed
when they are used as a higher-order function argument:
The expression |map<:Nat,Nat:> maybeDouble1 [1,3]<:Nat:>!|
evaluates to |[1,3]<:Nat:>!| or |[2,6]<:Nat:>!|.
This is because when |map| is called,
|maybeDouble1| is chosen to be |id<:Nat:>!| or |double|
due to call-time choice.
This means that it will act the same way on each list element.
On the other hand, the expression
|map<:Nat,Nat:> maybeDouble2 [1,3]<:Nat:>!|
evaluates to
|[1,3]<:Nat:>!|, |[1,6]<:Nat:>!|, |[2,3]<:Nat:>!| or |[2,6]<:Nat:>!|.
The reason is
that |maybeDouble2| is not \enquote{directly} nondeterministic,
only when applied to an argument.

\section{Formal Description of the Semantics}

When evaluating \cumin{} expressions,
we will have to keep track of variable assignments.

\begin{definition}[Heap]
A \emph{heap} is a mapping
|[x_1 /-> e_1, .., x_n /-> e_n]|
where the |x_i| are variables and
each |e_i| is either an expression or a special marker |free :: tau|,
in which case |x_i| is called a \emph{logic variable} of type |tau|.
Every variable that occurs in an expression |e_i|
has to be in the heap as well.

Given two heaps |Delta, Delta'| with disjoint variables,
one can form their \emph{union}.
It is written by juxtaposition: |Delta Delta'|.
\end{definition}

Every expression will be associated with a corresponding heap
that binds (at least) all the variables contained in the expression.

\begin{definition}[Heap Expression Pair]
A \emph{heap expression pair} |Delta : e| is
a heap |Delta| together with an expression |e|
such that every unbound variable occurring in |e| is in the heap |Delta|.
\end{definition}

The operational semantics will describe
how such heap expression pairs are evaluated.
In the most common case,
we want to know the value of an expression |e|
in the context of a certain \cumin{} program,
without a given heap.
In this case, we simply evaluate the heap expression pair |[] : e|.
When talking about evaluation,
one has to specify
when an expression is called \emph{evaluated}.
The following three notions will be useful:

\begin{definition}[Normal Forms]
An expression |e| (associated with a heap) is said to be
\begin{enumerate}
\item in \emph{flat normal form (FNF)}
if |e| is a literal,
a partial or full application
of a data constructor to heap variables,
or a partial application
of a top-level function |f| to heap variables.
\enquote{Partial} here means that the number of arguments given to |f|
is strictly smaller than the number of arguments
in the definition of the function |f|.
\item a \emph{value}
if |e| is in flat normal form or a logic variable.
\item in \emph{reduced normal form (RNF)}
if |e| is a literal,
a partial or full application
of a data constructor to expressions in reduced normal form,
or a partial application
of a top-level function to expressions in reduced normal form.
\end{enumerate}
\end{definition}

As an illustration, let us look at some expressions
in the context of the following heap.
> Delta := [ choice /-> free :: Bool, x /-> free :: Nat, y /-> x + x, n /-> Nil<:Bool:> ]
In this environment, |choice| is a value but not in FNF or RNF.
Furthermore, |Cons<:Bool:> choice n| is in FNF and thus also a value
but still not in RNF.
On the other hand, |Cons<:Bool:> True Nil<:Bool:>!| is in RNF
but neither in FNF nor a value
since |True| and |Nil<:Bool:>!| are not variables.
Additionally, there are terms like |2|, |Nil<:Nat:>!|, or |map<:Bool,Nat:>!|
that are values, in FNF and in RNF.

For each normal form, there is a corresponding evaluation strategy:
\begin{enumerate}
\item \emph{Logical evaluation},
denoted by |~>*|,
which evaluates to values,
\item \emph{Functional evaluation},
denoted by |~>|,
which evaluates to flat normal form.
\item \emph{Evaluation to reduced normal form},
denoted by |~>!| and sometimes also called \enquote{forcing}.
\end{enumerate}

These normal forms can be obtained by using the rules shown in
\cref{logical-eval,functional-eval,force-eval}.
\begin{figure}[p!]
\begin{tabularx}{\textwidth}{r >{\setstretch{1.8}}X}
{[Val]}
&\AxiomC{|Delta : v ~>* Delta : v|}
\DisplayProof
\hfill if |v| is a value \wrt |Delta|
\\[1em]
{[Lookup]}
&\AxiomC{|Delta: e ~>* Delta' : v|}
\UnaryInfC{|Delta[x /-> e]: x ~>* Delta'[x /-> v] : v|}
\DisplayProof
\hfill unless |x| is a logic variable
\\[1em]
{[Let]}
&\AxiomC{|Delta[y /-> e_1] : e_2[y/x] ~>* Delta' : v|}
\UnaryInfC{|Delta : let x = e_1 in e_2 ~>* Delta' : v|}
\DisplayProof
\hfill where |y| is fresh
\\[1em]
{[Free]}
&\AxiomC{|Delta[y /-> free :: tau] : e[y/x] ~>* Delta' : v|}
\UnaryInfC{|Delta : let x :: tau free in e ~>* Delta' : v|}
\DisplayProof
\hfill where |y| is fresh
\\[1em]
{[Fun]}
&\AxiomC{|Delta : e[vec (tau_m/alpha_m),vec (y_n/x_n)] ~>* Delta' : v|}
\UnaryInfC{|Delta : f <:vec tau_m:> (vec y_n) ~>* Delta' : v|}
\DisplayProof
\newline for a top-level function
|f ::forall (vec alpha_m) . (Data ..) => tau; f(vec x_n) = e|
\\[1em]
{[Flatten]}
&\AxiomC{|Delta: let y = e in phi y ~>* Delta' : v|}
\UnaryInfC{|Delta : phi e ~>* Delta' : v|}
\DisplayProof
\hfill where |phi| is in flat normal form and |y| fresh
\\[1em]
{[Apply]}
&\AxiomC{|Delta : e_1 ~>* Delta' : phi |}
\AxiomC{|Delta' : phi e_2 ~>* Delta'' : v|}
\BinaryInfC{|Delta : e_1 e_2 ~>* Delta'' : v|}
\DisplayProof
\\[1em]
{[Plus]}
&\AxiomC{|Delta : e_1 ~> Delta' : n_1|}
\AxiomC{|Delta' : e_2 ~> Delta'' : n_2|}
\BinaryInfC{|Delta : e_1 + e_2 ~>* Delta'' : n|}
\DisplayProof
\hfill for literals |n_1|, |n_2| and |n=n_1+n_2|
\\[1em]
{[EqNat]}
&\AxiomC{|Delta : e_1 ~> Delta' : n_1|}
\AxiomC{|Delta' : e_2 ~> Delta'' : n_2|}
\BinaryInfC{|Delta : e_1 == e_2 ~>* Delta'' : b|}
\DisplayProof
\newline where |n_1,n_2| are literals
and |b| is |True| if |n_1=n_2|, |False| otherwise.
\\[1em]
{[Eq]}
&\AxiomC{|Delta : e_1 ~> Delta' : C<:vec (tau_m):> (vec x_n)|}
\AxiomC{|Delta' : e_2 ~> Delta_0 : C<:vec (tau_m):> (vec y_n)|}
\AxiomC{|vec (Delta_nm1 : x_n == y_n ~> Delta_n : True)|}
\TrinaryInfC{|Delta : e_1 == e_2 ~> Delta_n : True|}
\DisplayProof
\\[1em]
{[NEq]}
&\AxiomC{|Delta : e_1 ~> Delta' : C<:vec (tau_m):> (vec x_n)|}
\AxiomC{|Delta' : e_2 ~> Delta_0 : C<:vec (tau_m):> (vec y_n)|}
\AxiomC{|vec (Delta<:i-1:> : x_i == y_i ~> Delta_i : b_i)|}
\TrinaryInfC{|Delta : e_1 == e_2 ~> Delta_i : False|}
\DisplayProof
\newline where $i \in \{1,\dots,n\}$
and |b_j| is |True| for all $j \in \{1,\dots,i-1\}$
but |b_i| is |False|.
\\[1em]
{[NEqCon]}
&\AxiomC{|Delta : e_1 ~> Delta' : C<:vec (tau_m):> (vec x_n)|}
\AxiomC{|Delta' : e_2 ~> Delta'' : D<:vec (tau_m):> (vec y_n)|}
\BinaryInfC{|Delta : e_1 == e_2 ~> Delta'' : False|}
\DisplayProof
\newline where |C| and |D| are different constructors.
\\[1em]
{[CaseCon]}
&\AxiomC{|Delta : e ~> Delta' : C<:vec tau_m:> (vec y_n)|}
\AxiomC{|Delta' : e'[vec y_n / vec x_n] ~>* Delta'' : v|}
\BinaryInfC{|Delta : case e of { ..; C (vec x_n) -> e'; .. } ~>* Delta'' : v|}
\DisplayProof
\\[1em]
{[CaseVar]}
&\AxiomC{|Delta : e ~> Delta' : C<:vec tau_m:> (vec x_n)|}
\AxiomC{|Delta'[y /-> C<:vec tau_m:> (vec x_n)] : e'[y/x] ~>* Delta'' : v|}
\BinaryInfC{|Delta : case e of { ..; x -> e' } ~>* Delta'' : v|}
\DisplayProof
\hfill where |y| is fresh
\newline Only applicable if none of the constructor patterns matched the constructor |C|.
\end{tabularx}
\caption{Rules for logical evaluation}
\label{logical-eval}
\end{figure}
\begin{figure}[t]
\begin{tabularx}{\textwidth}{r >{\setstretch{1.8}}X}
{[FNF]}
&\AxiomC{|Delta : e ~>* Delta' : v|}
\UnaryInfC{|Delta : e ~> Delta' : v|}
\DisplayProof
\hfill where |v| is in flat normal form
\\[1em]
{[Guess$_n$]}
&\AxiomC{|Delta: e ~>* Delta'[x :: Nat /-> free] : x|}
\UnaryInfC{|Delta: e ~> Delta'[x::Nat /-> n] : n |}
\DisplayProof
\hfill for any natural number |n|
\\[1em]
{[Guess$_|C|$]}
&\AxiomC{|Delta: e ~>* Delta'[x /-> free :: A (vec rho_m)] : x|}
\UnaryInfC{|Delta: e ~> Delta'[ vec (y_n /-> free :: tau_n[vec (rho_m/alpha_m)]), x /-> C<:vec rho_m:> (vec y_n)] : C<:vec rho_m:> (vec y_n)|} 
\DisplayProof
\hfill for any constructor |C| of the ADT |A (vec alpha_m)| with argument types |vec tau_n|
and where |vec y_n| are fresh variables
\end{tabularx}
\caption{Rules for functional evaluation}
\label{functional-eval}
\hrulefill
\end{figure}
\begin{figure}[t]
\begin{tabularx}{\textwidth}{r >{\setstretch{1.8}}X}
{[RNF]}
&\AxiomC{|Delta : e ~> Delta' : v|}
\UnaryInfC{|Delta : e ~>! Delta' : v|}
\DisplayProof
\hfill where |v| is in reduced normal form
\\[1em]
{[Force]}
&\AxiomC{|Delta : e ~> Delta_0 : f<:vec rho_m:> (vec y_n)|}
\AxiomC{|Delta_0 : y_1 ~>! Delta_1 : e_1|}
\AxiomC{\dots}
\AxiomC{|Delta_nm1 : y_n ~>! Delta_n : e_n|}
\QuaternaryInfC{|Delta: e ~>! Delta_n : f<:vec rho_m:> (vec e_n)|}
\DisplayProof
\newline where |f| is a constructor or top-level function
\end{tabularx}
\caption{Rules for evaluation to reduced normal form}
\label{force-eval}
\hrulefill
\end{figure}
Like the typing rules,
the evaluation rules are implicitly indexed by a given \cumin{} program.
This is again omitted from the notation for the sake of readability.
Another technicality to discuss is related to substitution:
A variable is called \emph{fresh} if its name does not occur
in the relevant expression and the \cumin{} program.
Since we only ever substitute with fresh variables in the evaluation rules,
variable capture (\cf \cref{sec:ast}) cannot happen.

\section{Explanation of the Semantics}
\label{sec:op-sem-explanation}

First note that the evaluation of an expression is not unique.
That is what nondeterminism is about, after all.
Some expressions can even evaluate to infinitely many values.
A simple example for that would be
\[
\AxiomC{|[x /-> free :: Nat] : x ~>* [x /-> free :: Nat] : x|}
\LeftLabel{\text{Guess$_n$}}
\UnaryInfC{|[x /-> free :: Nat] : x ~> [x /-> n] : n|}
\DisplayProof
\]
which works for any natural number |n|.

On the other hand, not every expression has a normal form.
A trivial example is |failed<:tau:>!|,
which simply has no applicable reduction rule.
This makes sense
because this expression denotes failure.
Having clarified that,
let us take a look at the individual rules of logical evaluation.
\begin{itemize}
\item \textbf{Val.}
If an expression is already a value,
it does not need to be evaluated further.
\item Rules related to variables:
  \begin{itemize}
  \item \textbf{Lookup.}
  Given a heap variable that is not a logic variable,
  evaluate the expression bound by the variable.
  Additionally, the heap must be updated
  to ensure sharing.
  This avoids recomputing the same expression repeatedly.
  Also, if the heap were not updated,
  a variable could nondeterministically evaluate to different values
  depending on where it is used,
  but instead, call-time choice is desired.
  \item \textbf{Let.}
  To evaluate a |let| binding,
  the bound variable and expression are added to the heap
  and the body is evaluated.
  The variable has to be replaced by a fresh name
  so that it will not shadow other heap variables.
  Note that the evaluation of the bound expression is deferred
  until it is needed (Lookup).
  This is \emph{lazy evaluation}.
  \item \textbf{Free.}
  Evaluating |let .. free| bindings works analogously.
  \end{itemize}
\item \textbf{Function application.}
There are three rules governing function application.
Together, they ensure the intended behavior:
lazy evaluation and call-time choice.
  \begin{itemize}
  \item \textbf{Fun.}
  This rule can be used whenever a top-level function is fully applied
  and its arguments are only heap variables.
  The function call is then replaced by the right hand side
  of the function definition,
  with variables and types properly substituted.
  The reason that the arguments must be variables is
  to ensure call-time choice and sharing.
  \item \textbf{Flatten.}
  To be able to apply the previous rule,
  all function arguments must be variables.
  This rule allows to achieve this by introducing |let| bindings.
  The argument of a function application is replaced
  by a fresh variable.

  Note that this rule can be applied
  even if all arguments are already variables.
  This unnecessary indirection is computationally undesirable
  but not forbidden according to this semantics.
  However, it is avoided in the implementation.
  \item \textbf{Apply.}
  The last rule for function application can always be applied.
  (However, it is only useful if the other rules don't make progress.)
  If the function is not already a top level function or constructor,
  but a more complex expression,
  this rule allows it to be evaluated to flat normal form.
  This way, after possibly having applied Flatten several times,
  the expression will be a value or have the shape required by Fun.
  \end{itemize}
\item \textbf{Plus.}
Addition is a primitive operation,
it has to deal with concrete numbers,
so its arguments must be in flat normal form.
Since they have type |Nat|,
they already have to be literals.
So to evaluate the expression,
the two arguments are evaluated \emph{functionally}
and the sum of the two literals is the result.
\item \textbf{Equality tests.}
In order to find out whether two expressions are equal,
they first have to be evaluated to at least flat normal form.
How evaluation continues, depends on the result.
  \begin{itemize}
  \item \textbf{EqNat.}
  If the resulting values are natural numbers,
  the comparison yields |True| if the numbers are equal,
  and |False| otherwise.
  \item \textbf{Eq.}
  If the resulting values are of an algebraic data type,
  they are equal if and only if
  their constructors match
  and each of their arguments are equal,
  which is checked recursively.
  \item \textbf{NEq.}
  If the constructors match,
  but some of their arguments are not equal,
  then evaluation stops at the first pair of arguments to differ.
  The remaining arguments are \emph{not} evaluated.
  The comparison yields |False|.
  \item \textbf{NEqCon.}
  If the constructors do not match,
  the comparison yields |False| immediately.
  No arguments are evaluated in this case.
  \end{itemize}
\item \textbf{Case expressions.}
In a case expression,
the first part to be evaluated is the scrutinee.
It has to be evaluated \emph{functionally}
since logic variables do not admit case analysis.
Since the type of the scrutinee is a data type,
it must be a fully applied constructor |C|.
One of the following two rules can be applicable.
  \begin{itemize}
  \item \textbf{CaseCon.}
  If one of the patterns in the case alternatives matches the constructor |C|,
  the corresponding expression is evaluated.
  Of course, the variables introduced in the constructor pattern
  must be replaced by the arguments of |C|.
  \item \textbf{CaseVar.}
  If none of the constructor patterns matched,
  the case alternative of a \enquote{catch-all} variable pattern
  (if there is one)
  is chosen.
  This acts just like a |let| binding,
  the only difference being that the bound expression
  is always in flat normal form.
  \end{itemize}
\end{itemize}

Functional evaluation essentially uses logical evaluation
and then takes care of logic variables if there are any.
In detail:

\begin{itemize}
\item \textbf{FNF.}
If the logical evaluation of an expression
is already in flat normal form,
this is also the result of functional evaluation.
\item \textbf{Guess$_n$.}
If an expression evaluates to a logic variable of type |Nat|,
its flat normal form is any natural number.
The value of the variable is updated on the heap, too.
\item \textbf{Guess$_C$.}
If an expression evaluates to a logic variable
with an algebraic data type,
its flat normal form is given by any constructor |C| of the ADT,
fully applied to new logic variables that are added to the heap.
The value of the original variable is updated on the heap, as before.
\end{itemize}

These last two rules are the source of nondeterminism.
Which constructor or which natural number is chosen for a logic variable
is not determined,
in contrast to the other rules
where choices do not affect the result.

Finally, the reduced normal form is obtained
by first evaluating functionally
and then reducing subexpressions as much as possible.
In detail:
\begin{itemize}
\item \textbf{RNF.}
If the functional evaluation of an expression
is already in reduced normal form,
there is nothing to be done.
\item \textbf{Force.}
If the flat normal form of an expression
is a constructor or function application,
all its arguments are forced to reduced normal form.
Then the result is in reduced normal form as well.
\end{itemize}

The operational semantics given above differs from \cite{cuminreport}
in that it supports general algebraic data types (not only lists and booleans),
case expressions with catch-all variable patterns,
and equality tests for arbitrary |Data| types, not only natural numbers.
Although it is based on \cite{ahhov} and \cite{bh},
these sources do not discriminate between functional and logic evaluation.
Moreover, they require the input programs to be in a certain normalized form
before they can be evaluated:
Nested constructor and function invocations have to be eliminated.
In the semantics given here, this normalization happens during evaluation,
by means of the Flatten rule.
The evaluation to reduced normal form is not explicitly described
in these sources,
but it is relatively straightforward
and makes the implementation of the semantics much more convenient to use.

\section{Examples}

In order to understand the evaluation rules better,
it is instructive to look at some examples.
Starting simple, let us look at the logical evaluation of |double 1|.
\begin{prooftree}
  \AxiomC{|[y /-> 1] : y ~>* [y /-> 1] : 1 |}
  \LeftLabel{Lookup}
  \UnaryInfC{|[y /-> 1] : y ~>* [y /-> 1] : 1 |}
  \LeftLabel{FNF}
  \UnaryInfC{|[y /-> 1] : y ~> [y /-> 1] : 1 |}
  \AxiomC{|[y /-> 1] : y ~>* [y /-> 1] : 1 |}
  \LeftLabel{Lookup}
  \UnaryInfC{|[y /-> 1] : y ~>* [y /-> 1] : 1 |}
  \LeftLabel{FNF}
  \UnaryInfC{|[y /-> 1] : y ~> [y /-> 1] : 1 |}
\LeftLabel{Plus}
\BinaryInfC{|[y /-> 1] : y + y ~>* [y /-> 1] : 2|}
\LeftLabel{Fun}
\UnaryInfC{|[y /-> 1] : double y ~>* [y /-> 1] : 2|}
\LeftLabel{Let}
\UnaryInfC{|[] : let x = 1 in double x ~>* [y /-> 1] : 2|}
\LeftLabel{Flatten}
\UnaryInfC{|[] : double 1 ~>* [y /-> 1] : 2|}
\end{prooftree}

Nondeterminism can lead to more than one result.
One of the simplest possible examples is
|let x :: Bool free in x|.
Its flat normal forms are |False| and |True|:
\begin{prooftree}
\AxiomC{|[y /-> free :: Bool] : y ~>* [y /-> free :: Bool] : y|}
\LeftLabel{Free}
\UnaryInfC{|[] : let x :: Bool free in x ~>* [y /-> free :: Bool] : y|}
\LeftLabel{Guess$_|False|$}
\UnaryInfC{|[] : let x :: Bool free in x ~> [y /-> False] : False|}
\end{prooftree}
\begin{prooftree}
\AxiomC{|[y /-> free :: Bool] : y ~>* [y /-> free :: Bool] : y|}
\LeftLabel{Free}
\UnaryInfC{|[] : let x :: Bool free in x ~>* [y /-> free :: Bool] : y|}
\LeftLabel{Guess$_|True|$}
\UnaryInfC{|[] : let x :: Bool free in x ~> [y /-> True] : True|}
\end{prooftree}

\subsection{The Coin Example}

As a more complex instance, consider |coin|.
As an abbreviation, let |Delta := [x' /-> 0, y' /-> 1]|
and |Delta' := Delta[c' /-> False]|.
\begin{prooftree}
  \AxiomC{\dots}
  \UnaryInfC{|[] : choose<:Bool:> 0 ~>* [x' /-> 0] : choose<:Bool:> x'|}
  \AxiomC{\dots}
  \UnaryInfC{|[x' /-> 0] : choose<:Bool:> x' 1 ~>* Delta' : 0|}
\LeftLabel{Apply}
\BinaryInfC{|[] : choose<:Bool:> 0 1 ~>* Delta' : 0|}
\LeftLabel{Fun}
\UnaryInfC{|[] : coin ~>* [c' /-> False] : 0|}
\end{prooftree}
The left subderivation continues as follows.
\begin{prooftree}
  \AxiomC{|[x' /-> 0] : choose<:Bool:> x' ~>* [x' /-> 0] : choose<:Bool:> x'|}
  \LeftLabel{Let}
  \UnaryInfC{|[] : let x = 0 in choose<:Bool:> x ~>* [x' /-> 0] : choose<:Bool:> x'|}
\LeftLabel{Flatten}
\UnaryInfC{|[] : choose<:Bool:> 0 ~>* [x' /-> 0] : choose<:Bool:> x'|}
\end{prooftree}
The right subderivation goes on like this.
\begin{prooftree}
    \AxiomC{|Delta[c' /-> free :: Bool] : c' ~>* Delta[c' /-> free :: Bool] : c'|}
    \LeftLabel{Guess$_|False|$}
    \UnaryInfC{|Delta[c' /-> free :: Bool] : c' ~> Delta' : False|}
    \AxiomC{|Delta' : 0 ~>* Delta' : 0|}
  \LeftLabel{CaseCon}
  \BinaryInfC{|Delta[c' /-> free :: Bool] : case c' of { False -> 0; .. } ~>* Delta' : 0|}
  \LeftLabel{Free}
  \UnaryInfC{|Delta : let c :: Bool free in case c of { False -> 0; True -> 1 } ~>* Delta' : 0|}
  \LeftLabel{Fun}
  \UnaryInfC{|Delta : choose<:Bool:> x' y' ~>* Delta' : 0|}
  \LeftLabel{Let}
  \UnaryInfC{|[x' /-> 0] : let y = 1 in choose<:Bool:> x' y ~>* Delta' : 0|}
\LeftLabel{Flatten}
\UnaryInfC{|[x' /-> 0] : choose<:Bool:> x' 1 ~>* Delta' : 0|}
\end{prooftree}

A completely analogous derivation
that uses Guess$_|True|$ instead of Guess$_|False|$
yields the other evaluation |[] : coin ~>* Delta[c' /-> True] : 1|.

\subsection{Call-time Choice}

In the introduction of this chapter,
we discussed the examples |coin + coin| and |let c = coin in c + c|.
Let us find out how the difference between them manifests itself.
\begin{prooftree}
    \AxiomC{\dots}
    \UnaryInfC{|[] : coin ~>* Delta : i|}
  \LeftLabel{FNF}
  \UnaryInfC{|[] : coin ~> Delta : i|}
    \AxiomC{\dots}
    \UnaryInfC{|Delta : coin ~>* Delta' : j|}
  \LeftLabel{FNF}
  \UnaryInfC{|Delta : coin ~> Delta' : j|}
\LeftLabel{Plus}
\BinaryInfC{|[] : coin + coin ~>* Delta' : i + j|}
\end{prooftree}
This derivation works for all $i = 0, 1$ and $j = 0, 1$.
Thus, the possible results are 0, 1 and 2.
In contrast, consider the derivation for |let c = coin in c + c|.
\begin{prooftree}
    \AxiomC{\dots}
    \UnaryInfC{|[c' /-> coin] : coin ~> Delta[c' /-> i] : i|}
    \LeftLabel{Lookup}
    \UnaryInfC{|[c' /-> coin] : c' ~>* Delta[c' /-> i] : i|}
  \LeftLabel{FNF}
  \UnaryInfC{|[c' /-> coin] : c' ~> Delta[c' /-> i] : i|}
    \AxiomC{|Delta[c' /-> i] : c' ~>* Delta[c' /-> i] : i|}
    \LeftLabel{Lookup}
    \UnaryInfC{|Delta[c' /-> i] : c' ~>* Delta[c' /-> i] : i|}
  \LeftLabel{FNF}
  \UnaryInfC{|Delta[c' /-> i] : c' ~> Delta[c' /-> i] : i|}
\LeftLabel{Plus}
\BinaryInfC{|[c' /-> coin] : c' + c' ~>* Delta[c' /-> i] : i + i|}
\LeftLabel{Let}
\UnaryInfC{|[] : let c = coin in c + c ~>* Delta[c' /-> i] : i + i|}
\end{prooftree}
Again, this works for all $i = 0, 1$.
But the two summands are not independent in this case.
Hence, the only possible results are 0 and 2.

\subsection{Reduced Normal Form}

So far, we have not dealt with |~>!|.
For sake of completeness, we will analyze
how |let y :: List Bool free in y| can evaluate to
|Cons<:Bool:> True Nil<:Bool:>!|.
For lack of space, the heaps are omitted.
Nevertheless, the idea should become clear.
\begin{prooftree}
    \AxiomC{(as above \dots)}
    \LeftLabel{Free}
    \UnaryInfC{|let .. ~>* y'|}
  \LeftLabel{Guess$_|Cons|$}
  \UnaryInfC{|let .. ~> Cons<:Bool:> x xs|}
    \AxiomC{\dots}
    \LeftLabel{FNF}
    \UnaryInfC{|x ~>* x|}
    \LeftLabel{Guess$_|True|$}
    \UnaryInfC{|x ~> True|}
  \LeftLabel{RNF}
  \UnaryInfC{|x ~>! True|}
    \AxiomC{\dots}
    \LeftLabel{FNF}
    \UnaryInfC{|xs ~>* xs|}
    \LeftLabel{Guess$_|Nil|$}
    \UnaryInfC{|xs ~> Nil<:Bool:>|}
  \LeftLabel{RNF}
  \UnaryInfC{|xs ~>! Nil<:Bool:>|}
\LeftLabel{Force}
\TrinaryInfC{|let x :: List Bool free in x ~>! Cons<:Bool:> True Nil<:Bool:>|}
\end{prooftree}

The different choices of the applied Guess rules
can be visualized in a tree like this.

\begin{center}
\small
\Tree [.|free :: List Bool|
  [.|Nil<:Bool:>| ]
  [.|Cons<:Bool:> (free :: Bool) (free :: List Bool)|
    [.|Cons<:Bool:> False (free :: List Bool)|
      [.$\quad\vdots\quad$ ]
      [.$\quad\vdots\quad$ ]
    ]
    [.|Cons<:Bool:> True (free :: List Bool)|
      [.|Cons<:Bool:> True Nil<:Bool:>| ]
      [.|Cons<:Bool:> True (Cons<:Bool:> ..)|
        [.$\quad\vdots\quad$ ]
        [.$\quad\vdots\quad$ ]
      ]
    ]
  ]
]
\end{center}

\section{Implementation}

\subsection{Nondeterminism and Search}

While the operational semantics formalizes
which evaluations are valid,
it does not directly specify
how all the nondeterministic results of a computation can be found,
\ie what constructors should be chosen in the Guess rules
and in what order.
As we have seen in the previous section,
trees are a natural representation for this.

The implementation of the semantics is thus split into two components:
the actual evaluation of an expression,
which generates such an evaluation tree;
and the traversal of this tree,
for example using depth-first or breadth-first search.
This may sound inefficient at first,
as only parts of the generated tree may actually be needed.
However, since Haskell is a lazy language,
the tree is generated on demand,
while being traversed.
In this way, laziness allows decoupling evaluation and search.

\subsection{Evaluation}

Before explaining the actual implementation,
I have to describe how the various objects and normal forms
where modeled as data types.

A heap is represented as a standard map data structure (Data.Map)
with variable names (strings) as keys and expressions as values.
The normal forms are algebraic data types, as expected.
\begin{code}
data FNF
  = PartialApp BindingName [Type] [VarName]
  | ConValue DataConName [Type] [VarName]
  | Literal Lit

data Value
  = Fnf FNF
  | Logic VarName Type
\end{code}
Furthermore, there are (among others) the following evaluation functions.
> evaluateFunctionally  :: Exp -> EvalT TreeM FNF
> evaluateLogically     :: Exp -> EvalT TreeM Value
These functions accept a \cumin{} expression
and produce a tree with all possible results at the leaves,
flat normal forms and values, respectively.
|EvalT| is a monad transformer \cite{monad-transformers}
that manages the state of the computation,
namely the heap and a counter for generating fresh names,
as well as an environment
with the data types and functions of the \cumin{} program.
|TreeM| is a monad that supports nondeterminism
by building an evaluation tree.
|EvalT TreeM| is a monad
that combines these stateful and nondeterministic effects.
This way, one does not have to manage
the state and trees explicitly throughout the computation;
it is instead handled by the monadic bind operation.

As for the implementation of the evaluation rules,
there are some details to be discussed.
First, the rules often require fresh variables to be added to the heap.
To guarantee that all variables are fresh,
every new variable name includes the current value of a counter
which is increased afterwards,
hence ensuring that all generated variables are unique.
Avoiding variable capture on substitution (\cf \cref{sec:ast})
has to be taken care of as well.
In this case, however, it is not an issue
since one only ever substitutes fresh variables for existing ones.

In most cases, the shape of an expression determines
the next evaluation rule to apply.
For instance, if it is an addition,
only the Plus rule can be applied.
In other cases, like in case expressions or equality tests,
parts of the expression have to be evaluated,
and then there is only one rule that matches.
Logic variables are inherently nondeterministic,
so in this case more than one rule is applicable,
and the evaluation tree branches.
The only remaining case is function application.
The rules Fun, Apply, Flatten can be employed
and there may be more than one choice.
The implementation uses the following strategy:
It applies the Fun rule first, whenever possible.
If not, it tries the Apply rule.
In case this also had no effect,
it uses the Flatten rule.
This strategy always makes progress (\cf \cref{sec:op-sem-explanation}).

All in all, logical evaluation proceeds like this:
It checks whether the expression is already a value,
and if so, does nothing (Val rule).
Otherwise, depending on the shape of the expression,
a suitable rule is applied according to the details
in the previous paragraph.
Functional evaluation invokes logical evaluation first.
If the result is already in flat normal form,
nothing has to be done (FNF rule).
Otherwise, the result is a logic variable
which results in a branching of the evaluation tree,
one new branch for each applicable Guess rule.
Evaluation to reduced normal form uses functional evaluation.
If the result is in RNF, nothing is to be done (RNF rule).
Otherwise, the subexpressions are recursively forced (Force rule).

One more thing to discuss is guessing natural numbers.
One could simply generate them in a tree like this:
\begin{center}
\small
\Tree [.|free :: Nat|
  [.|0| ]
  [.|1| ]
  [.|2| ]
  [.|..| ]
]
\end{center}
The disadvantage is that breadth-first search will not
find all solutions on such a tree
since it contains a node with infinitely many direct children.
As completeness of BFS is desirable,
the program will instead generate a tree
with only finitely many nodes on each level,
namely the numbers with $i$ bits on the $i$-th level.
This tree also yields the same result,
independently of whether BFS or DFS is used:
\begin{center}
\small
\Tree [.|free :: Nat|
  [.|0| ]
  [. {$\geq 1$ bits}
    [. |1| ]
    [. {$\geq 2$ bits}
      [. |2| ]
      [. |3| ]
      [. {$\geq 3$ bits}
        [. |4| ]
        [. |5| ]
        [. |6| ]
        [. |7| ]
        [. $\vdots$ ]
      ]
    ]
  ]
]
\end{center}

\subsection{Trees and Traversals}

An evaluation tree is represented by the data type
> data Tree a = Leaf a | Branches [Tree a]
It can be made a monad\footnote{
In fact, this type constructor represents
the free monad over the list functor.},
\ie there are two functions |return :: a -> Tree a|
and |(>>=) :: Tree a -> (a -> Tree b) -> Tree b|.
The former simply creates a leaf
and the bind operation |>>=| performs substitution on the leaves.
The operation that is important for nondeterminism is given by the function
> branch :: [a] -> Tree a
> branch = Branches . map Leaf
which creates a tree with the given leaves.
Failure is represented by a tree without leaves:
> failure :: Tree a
> failure = branch []
In order to better understand how these functions work,
consider the following code sample.
> branch [0,10] >>= \x -> branch [1,2,3] >>= \y -> return (x + y)
There is special notation for |>>=| in Haskell,
which allows it to be rewritten like this.
> do  x <- branch [0,10]
>     y <- branch [1,2,3]
>     return (x + y)
The code produces the tree visualized below.
As the example demonstrates,
|branch| produces the nondeterminism,
and the monadic structure of |Tree| hides the composition of this effect,
namely the substitution of trees.
\begin{center}
\Tree [. {}
  [. |0|
    [. |0 + 1| ]
    [. |0 + 2| ]
    [. |0 + 3| ]
  ]
  [. |10|
    [. |10 + 1| ]
    [. |10 + 2| ]
    [. |10 + 3| ]
  ]
]
\end{center}

However, this tree structure performed rather badly.
Profiling the application revealed
that most of the time was spent performing substitution on the tree.
This takes a lot of time for deep trees
since it has to be traversed completely to get to the leaves.
This problem turns out to be well-known \cite{codensity}.
The solution is called the \emph{codensity transformation}.
It works by \enquote{focusing} on the leaves of the tree
to speed up substitution.
The transformed type looks like this:
> newtype CTree a = CTree (forall r. (a -> Tree r) -> Tree r)
It represents the tree by a function
taking a function of type |a -> Tree r|
which, when applied to the leaves of the |CTree a|,
yields a |Tree r|.
It can be given a monad instance
that performs much better.
For certain evaluation trees with lots of branches,
it was more than ten times faster.
Such a |CTree| is converted to a |Tree| after construction,
so that it can be traversed.

I implemented two kinds of traversals for evaluation trees:
breadth-first search and depth-first search,
each with and without a depth limit.
Each of them has advantages and drawbacks.
Depth-first search is incomplete:
In many infinite trees,
not every solution will be found in finite time.
Breadth-first search is complete
but uses more memory.
A more detailed comparison of the two
can be found in \cref{sec:op-sem-assessment}.

It was mentioned before that the monad |EvalT TreeM|
combines the nondeterministic effects of trees
with the stateful effects of the |EvalT| monad transformer.
The implementation of the Guess rule for natural numbers
demonstrates such a usage.
The part of the function that generates the evaluation tree
for a logic variable |v| is given below in a slightly simplified form.
\begin{code}
do  n <- lift (branchNatLongerThan 0)
    updateVarOnHeap v (ELit (LNat n))
    return (Literal (LNat n))
\end{code}
In the following explanation, I will omit some technical details,
such as the |lift| function,
but it should give a rough idea of how it works:
The expression |branchNatLongerThan 0| uses |branch| internally
to create the evaluation tree for natural numbers
that was discussed in the previous section.
For every natural number |n| in this tree,
|updateVarOnHeap| sets the value of the variable |v| on the heap
to the literal |n|, in each branch of the computation.
Finally, the result of the computation is given
by the literal |n|, which is in flat normal form.
This example combines both nondeterministic and stateful effects,
triggered by functions like |branch| or |updateVarOnHeap|.
One does not have to manually propagate them through the program,
which makes the actual computation much clearer.

\subsection{REPL}

As an interface to the evaluation functions,
I created a REPL (read-evaluate-print-loop)
where the user can enter expressions
and have them evaluated.

The REPL can evaluate expressions functionally,
when given the commands \verb!:e! or \verb!:eval!,
printing the results together with the corresponding heap.
When no command is given, it evaluates expressions to reduced normal form.
This can also be explicitly specified
by the commands \verb!:f! or \verb!:force!.
In this case, the heap is unnecessary,
since there are no variables in the reduced normal form.
The expressions are type checked before evaluation
and the computation time is displayed afterwards.
Evaluation can also be interrupted with the key combination \verb!Ctrl + C!,
which is useful for non-terminating expressions.
To quit the REPL, the user should type \verb!:q! or \verb!:quit!.

There are two parameters that the user can change,
namely the search depth limit, which is infinity by default,
and the search strategy, which is BFS by default.
The values of the parameters can be viewed with \verb!:get!
and they can be changed using \verb!:set!.

As an illustration,
let us have a look at an example session.
The REPL was loaded with the file \verb!List.cumin!,
which contains the function |last| from the introduction,
as a command-line argument.

{\small
\begin{verbatim}
Type ":h" (without quotes) for help.
Loaded module `List`.
> :h
List of commands:
 * :h, :help
        Show this help text.
 * :q, :quit
        Quit the program.
 * :r, :reload
        Reload the current module.
 * :f <expr>, :force <expr>, <expr>
        Force the expression <expr> to reduced normal form.
 * :e <expr>, :eval <expr>
        Evaluate the expression <expr> to flat normal form.
 * :g, :get
        List all configurable properties and their current values.
 * :s <prop>=<val>, :set <prop>=<val>
        Set property <prop> to value <val>. For details use ':get'.
> last<:Bool:> [True, False]<:Bool:>
 :: Bool
 = False<::>

CPU time elapsed: 0.000 s
> let x :: Bool free in x
 :: Bool
 = False<::>
 = True<::>

CPU time elapsed: 0.000 s
> choose<:Bool:> True False
 :: Bool
 = True<::>
 = False<::>

CPU time elapsed: 0.000 s
> :get
Current settings:
 * depth=inf:
   The search depth limit. Values: inf, 0, 1, 2, ...
 * strategy=bfs:
   The search strategy: bfs, dfs
> :set depth=3
> let x :: List Bool free in x
 :: List Bool
 = Nil<:Bool:>
 = Cons<:Bool:> False<::>
     Nil<:Bool:>
 = Cons<:Bool:> True<::>
     Nil<:Bool:>

CPU time elapsed: 0.000 s
> :e let x :: List Bool free in x
 :: List Bool
 ~> [_1_x -> Nil<:Bool:>]
      : Nil<:Bool:>
 ~> [_1_x -> Cons<:Bool:>
    _2_conArg _3_conArg
    ,_2_conArg -> free :: Bool
    ,_3_conArg -> free :: List Bool]
      : Cons<:Bool:> _2_conArg
      _3_conArg

CPU time elapsed: 0.000 s
> :q
Bye.
\end{verbatim}
}

The sample session demonstrates the evaluation of a deterministic example,
namely the |last| function,
and nondeterministic examples with logic variables.
In the latter case, evaluation has more than one result,
and all of them are displayed.
The use of \verb!:get! shows the default strategy and search depth limit.
Afterwards, the latter is set to 3 with the \verb!:set! command.
Only because of that, the next evaluation terminates,
yielding three boolean lists.
Without the depth limit, there would be an infinite number of results.
While all expressions so far were evaluated to reduced normal form,
the last example uses the command \verb!:e! to evaluate only to flat normal form.
As a consequence, the results are not fully evaluated,
\eg the |Cons| constructor is applied to logic variables on the heap.

The REPL is implemented using the \emph{Haskeline} library\footnote{
\url{https://hackage.haskell.org/package/haskeline}},
which is also used by GHCi,
the REPL of the Glasgow Haskell compiler.
It provides a history of the previous inputs
that can be selected using the up and down keys.

\subsection{Testing}

In order to verify the correctness of the interpreter,
I created a test-suite called \verb!cumin-test! in the implementation.
It performs two kinds of checks:
First, it evaluates certain test expressions to reduced normal form,
and compares them with the corresponding expected results.
As a second check, I used a denotational semantics for \cumin{},
implemented by Fabian Thorand in his bachelor thesis.
The test expressions are also evaluated using this implementation,
and it is checked whether the results agree with the operational semantics.

\section{Assessment of the Search Strategies}
\label{sec:op-sem-assessment}

To examine the effect of different search strategies,
I created a benchmark\footnote{
a separate executable in the implementation, called \verb!cumin-bench!}
with some test programs and measured the time
to evaluate certain nondeterministic expressions
to reduced normal form
using breadth-first search or depth-first search, respectively.
The test expressions were the following:
\begin{itemize}
\item
subtracting two natural numbers in Peano representation\footnote{
A Peano number is either zero or represented as the successor of another Peano number: |data Peano = Zero || Succ Peano|.}
using a free variable and addition,
\item
dividing two Peano numbers using a free variable and multiplication,
\item
finding the last element of a 20-element list of boolean values,
as shown in the introduction,
\item
sorting a four-element list of Peano numbers by trying all permutations,
\item
subtracting two primitive natural numbers using a logic variable and addition and
\item
multiplying two primitive natural numbers $m,n$
in terms of subtraction: $mn = n + (m-1)n$.
\end{itemize}
For the last two test cases, evaluation was stopped
as soon as the first solution was found.
In the other cases, the evaluation tree had to be searched exhaustively.

To determine the execution times (wall-clock time),
I used the benchmarking library \verb!criterion!\footnote{
\url{http://http://hackage.haskell.org/package/criterion}}.
By running the benchmarks many times,
it can accurately measure even very short running times.
The program was compiled by GHC 7.8.3 with optimizations enabled (\verb!-O2!).
The results are shown in \cref{perf-bfs-dfs}.
\begin{figure}[t]
\centering
\begin{tabular}{l l l l}
Program & All results computed? & DFS & BFS \\
\hline
Peano subtraction & all results & 78\,ms & 72\,ms \\
Peano division & all results & 110\,ms & 110\,ms \\
Last & all results & 2.3\,ms & 2.2\,ms \\
Permutation sort & all results & 3.9\,ms & 4.0\,ms \\
\hline
|Nat| subtraction & only the first one & 38\,ms & 39\,ms \\
|Nat| multiplication & only the first one & 0.28\,ms & 58\,ms
\end{tabular}
\caption{Average running times with different search strategies}
\label{perf-bfs-dfs}
\hrulefill
\end{figure}

As one can see, in most test cases,
DFS and BFS take approximately the same time.
However, in the last case, DFS is significantly faster.
The reason for that is that the only successful \enquote{leaf}
in the computation tree is at a certain place
which is explored much earlier by DFS than by BFS.
However, in other scenarios, the situation may be reversed
since DFS can \enquote{get stuck} in a branch that does not yield a solution.

BFS has the theoretical disadvantage of worse space complexity than DFS.
But in the examples I tested, this did not seem to be a problem.
On the other hand, it has the advantage of
finding all solutions even in infinitely deep trees.
Therefore, it seems to be preferable as a default search strategy.
