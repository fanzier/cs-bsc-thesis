\chapter{Operational Semantics for \cumin{}}

Having defined
what well-formed \cumin{} programs look like,
we want to define what they \emph{mean}.
That means, we want to give them a \emph{semantics}.
There are two kinds of semantics,
\emph{denotational} and \emph{operational}.
A denotational semantics describes
the meaning of expressions
as mathematical objects.
Denotational semantics for \cumin{} and \salt{}
were given in \cite{orig}
and were implemented by Fabian Thorand in his bachelor thesis.

The other approach to the meaning of programming languages
are operational semantics.
These describe the program's execution directly,
instead of translating it to mathematical objects.
An operational semantics for (a subset of) Curry can be found in \cite{bh},
which is a modification of \cite{ahhov}.
Based on this,
Stefan Mehner describes such a semantics
for the variant of \cumin{} without algebraic data types,
as in \cite{orig}.
A few small changes and generalizations lead to the semantics below.

\section{Formal Description}

When evaluating \cumin{} expressions,
we will have to keep track of variable assignments.

\todo[inline]{Keep track of types in heap???}

\begin{definition}[Heap]
A \emph{heap} is a finite sequence of variable bindings
|[x_1 /-> e_1, .., x_n /-> e_n]|
where each |e_i| is either an expression or a special marker |free :: tau|,
in which case |x_i| is called a \emph{logic variable} of type |tau|.
\end{definition}

Every expression will be associated with a corresponding heap
that binds (at least) all the variables in the expression.

\begin{definition}[Heap Expression Pair]
A \emph{heap expression pair} |Delta : e| is
a heap |Delta| together with an expression |e|.
\end{definition}

The operational semantics will describe
how such heap expression pairs are evaluated.
When talking about evaluation,
one has to specify
when an expression is called evaluated.
The following two notions will be useful:

\begin{definition}[Normal Forms]
An expression |e| is said to be
\begin{enumerate}
\item in \emph{flat normal form}
if |e| is a literal
or a partial or full application
of a data constructor to heap variables
or a partial application
of a top-level function |f| to heap variables.
\enquote{Partial} here means that the number of arguments of |f| in |e|
is strictly smaller than the number of arguments
in the definition of the function |f|.
\item a \emph{value}
if |e| is in flat normal form or a logic variable.
\item in \emph{reduced normal form}
if |e| is in flat normal form
and each argument of the data constructor or top-level function
is itself in reduced normal form.
Reducing an expression to this normal form is also called \emph{forcing}.
\end{enumerate}
\end{definition}

\todo[inline]{Add examples!}

There are three kinds of evaluation:
\begin{enumerate}
\item \emph{Logical evaluation},
denoted by |~>*|,
which evaluates to values,
\item \emph{Functional evaluation},
denoted by |~>|,
which evaluates to flat normal form.
\item \emph{Evaluation to reduced normal form},
denoted by |~>!|.
This is sometimes also called \enquote{forcing}.
\end{enumerate}

How can these normal forms be obtained?
This is done using the rules below.
The rationale behind them is explained in the next section.

\begin{enumerate}
\item[Val] 
\AxiomC{|Delta : v ~>* Delta : v|}
\DisplayProof
\hfill if |v| is a value \wrt |Delta|

\item[Lookup]
\AxiomC{|Delta: e ~>* Delta' : v|} 
\UnaryInfC{|Delta[x /-> e]Omega: x ~>* Delta'[x /-> v]Omega : v|}
\DisplayProof
\hfill unless |x| is a logic variable

\item[Let]
\AxiomC{|Delta[y /-> e_1] : e_2[y/x] ~>* Delta' : v|}
\UnaryInfC{|Delta : let x = e_1 in e_2 ~>* Delta' : v|}
\DisplayProof
\hfill where |y| is fresh

\item[Free]
\AxiomC{|Delta[y /-> free :: tau] : e[y/x] ~>* Delta' : v|}
\UnaryInfC{|Delta : let x :: tau free in e ~>* Delta' : v|}
\DisplayProof
\hfill where |y| is fresh

\item[Fun]
\AxiomC{|Delta : e[vec (tau_m/alpha_m),vec (y_n/x_n)] ~>* Delta' : v|}
\UnaryInfC{|Delta : f <:vec tau_m:> (vec y_n) ~>* Delta' : v|}
\DisplayProof
\hfill for a top-level function
|f ::forall alpha_1 ..  alpha_m . tau; f(vec x_n) = e|

\item[Flatten]
\AxiomC{|Delta: let y = e in phi y ~>* Delta' : v|}
\UnaryInfC{|Delta : phi e ~>* Delta' : v|}
\DisplayProof
\hfill where |phi| is in flat normal form and |y| fresh

\item[Apply]
\AxiomC{|Delta : e_1 ~>* Delta' : phi |}
\AxiomC{|Delta' : phi e_2 ~>* Delta'' : v|}
\BinaryInfC{|Delta : e_1 e_2 ~>* Delta'' : v|}
\DisplayProof

\item[Plus]
\AxiomC{|Delta : e_1 ~> Delta' : n_1|}
\AxiomC{|Delta' : e_2 ~> Delta'' : n_2|}
\BinaryInfC{|Delta : e_1 + e_2 ~>* Delta'' : n|}
\DisplayProof
\hfill for literals |n_1|, |n_2| and |n=n_1+n_2|

\item[Eq]
\AxiomC{|Delta : e_1 ~> Delta' : n_1|}
\AxiomC{|Delta' : e_2 ~> Delta'' : n_2|}
\BinaryInfC{|Delta : e_1 == e_2 ~>* Delta'' : b|}
\DisplayProof
\hfill for literals |n_1|, |n_2|
and |b = n_1 == n_2|

\item[CaseCon]
\AxiomC{|Delta : e ~> Delta' : C<:vec tau_m:> (vec y_n)|}
\AxiomC{|Delta' : e'[vec y_n / vec x_n] ~>* Delta'' : v|}
\BinaryInfC{|Delta : case e of { ..; C (vec x_n) -> e'; .. } ~>* Delta'' : v|}
\DisplayProof
\hfill where |C| is the only matching constructor
in the case alternatives.

\item[CaseVar]
\AxiomC{|Delta : e ~> Delta' : C<:vec tau_m:> (vec x_n)|}
\AxiomC{|Delta'[x /-> C<:vec tau_m:> (vec x_n)] : e ~>* Delta'' : v|}
\BinaryInfC{|Delta : case e of { ..; x -> e } ~>* Delta'' : v|}
\DisplayProof
\hfill only if none of the constructor patterns
before the catch-all pattern |x| matched the constructor |C|.

\bigskip

\item[FNF]
\AxiomC{|Delta : e ~>* Delta' : v|}
\UnaryInfC{|Delta : e ~> Delta' : v|}
\DisplayProof
\hfill where |v| is in flat normal form

\item[Guess$_n$]
\AxiomC{|Delta: e ~>* Delta'[x :: Nat /-> free]Omega : x|}
\UnaryInfC{|Delta: e ~> Delta'[x::Nat /-> n]Omega : n |} 
\DisplayProof
\hfill for any literal |n|

\item[Guess$_|C|$]
\AxiomC{|Delta: e ~>* Delta'[x /-> free :: A rho_1 .. rho_m]Omega : x|}
\UnaryInfC{|Delta: e ~> Delta'[ vec (y_n /-> free :: tau_n), x /-> C<:rho_1, .., rho_m:> (vec y_n)]Omega : C<:rho_1, .., rho_m:> (vec y_n)|} 
\DisplayProof
\hfill for any constructor |C| of the ADT |A|
and where |C<:rho_1,..,rho_m:>| has argument types |tau_n|
and |vec y_n| are fresh variables
\end{enumerate}

\begin{enumerate}
\item[RNF]
\AxiomC{|Delta : e ~> Delta' : v|}
\UnaryInfC{|Delta : e ~>! Delta' : v|}
\DisplayProof
\hfill where |v| is in reduced normal form

\item[Force]
\AxiomC{|Delta : e ~> Delta_0 : f<:rho_1, .., rho_m:> y_1 .. y_n|}
\AxiomC{|Delta_0 : y_1 ~>! Delta_1 : e_1|}
\AxiomC{\dots}
\AxiomC{|Delta_nm1 : y_n ~>! Delta_n : e_n|}
\QuaternaryInfC{|Delta: e ~>! Delta_n : f<:rho_1, .., rho_m:> e_1 .. e_n|} 
\DisplayProof
\hfill where |f<:rho_1,..,rho_m:>| is a constructor or top-level function
\end{enumerate}

\section{Explanation of the Semantics}

First note that the evaluation of an expression is not unique.
Some expressions even can evaluate to infinitely many values
-- that is what non-determinism is about, after all.
A trivial example for that would be
\[
\AxiomC{|[x /-> free :: Nat] : x ~>* [x /-> free :: Nat] : x|}
\LeftLabel{\text{Guess$_n$}}
\UnaryInfC{|[x /-> free :: Nat] : x ~> [x /-> n] : n|}
\DisplayProof
\]
which works for any natural number |n|.

On the other hand, not every expression has a normal form.
A trivial example is |failed<:tau:>|,
which simply has no applicable reduction rule.
This makes sense
because this expression denotes failure.

Having cleared this up,
let us take a look at the individual rules of logical evaluation.
\begin{itemize}
\item \textbf{Val.}
If an expression is already a value,
it does not need to be evaluated further.
\item Rules related to variables
  \begin{itemize}
  \item \textbf{Lookup.}
  Given a heap variable that is not a logic variable,
  evaluate the expression bound by the variable.
  Additionally, the heap must be updated
  to ensure sharing.
  This way, we want to avoid recomputing the same expression repeatedly.
  Also, if the heap were not updated,
  a variable could non-deterministically evaluate to different values
  depending on where it is used.
  \item \textbf{Let.}
  To evaluate a |let| binding,
  the bound variable and expression are added to the heap
  and the rest of the expression is evaluated.
  The variable has to be replaced by a fresh name
  so that it won't shadow other heap variables.
  Note that the evaluation of the bound expression is deferred
  until it is needed. (\emph{lazy evaluation})
  \item \textbf{LetFree.}
  Evaluating |let .. free| bindings work completely analogously.
  \end{itemize}
\item \textbf{Function application}
  \begin{itemize}
  \item \textbf{Fun.}
  This rule can be used whenever a top-level function is fully applied
  and its arguments are only heap variables.
  The function call is then replaced by the right hand side
  of the function definition,
  with variables and types properly substituted.
  The reason that the arguments must be variables is
  to ensure that the arguments are shared.
  This strately is known as \emph{call-time choice}.
  \item \textbf{Flatten.}
  To be able to apply the previous rule,
  all function arguments must be variables.
  This rule allows to achieve this by introducing |let| bindings.
  The argument of a function application is replaced
  by a fresh variable.

  Note that this rule could be applied
  even if all arguments are already variables.
  This unnecessary indirection is computationally undesirable
  but not forbidden according to this semantics.
  However, it is avoided by the interpreter.
  \item \textbf{App.}
  The last rule for function application can always be applied.
  (However, it is only useful if the other rules don't make progress.)
  If the function is not already a top level function or constructor
  but a more complex expression,
  this rule allows the it to be evaluated to flat normal form.
  This way, after possibly having applied Flatten several times,
  the expression will be a value or have the shape required by Fun.
  \end{itemize}
  \item \textbf{Primitive operations}
  \begin{itemize}
  \item \textbf{Plus.}
  Addition is a primitive operation,
  it has to deal with concrete numbers,
  so its arguments must be in flat normal form.
  Since they have type |Nat|,
  they already have to be literals.
  So to evaluate the expression,
  the two arguments are evaluated \emph{functionally}
  and the sum of the two literals is the result.
  \item \textbf{Eq.}
  Equality tests work completely analogously.
  \end{itemize}
\item \textbf{Case expressions.}
In a case expression,
the first part to be evaluated is the scrutinee.
It has to be evaluated \emph{functionally}
since logic variables do not allow case analysis.
Because the type of the scrutinee is a data type,
it must be a fully applied constructor |C|.
One of the following two rules is applicable.
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
  is already in flat normal form.
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
The value of the variable is updated on the heap, as before.
\item \textbf{Guess$_C$.}
If an expression evaluates to a logic variable
with an algebraic data type,
its flat normal form is given by any constructor |C| of the ADT,
fully applied to logic variables that are added to the heap.
The value of the original variable is updated on the heap, as before.
\end{itemize}

These last two rules are the source of non-determinism.
Which constructor or which natural number is chosen for a logic variable
is not determined;
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
force all its arguments to reduced normal form.
The result is in reduced normal form.
\end{itemize}

\section{Examples}

\todo[inline]{Add examples!}

\section{Implementation}

\section{Evaluation}
