\chapter{Translating \cumin{} to \salt{}}

\cumin{} is convenient
because nondeterminism is implicit.
On the other hand,
this makes it harder to analyze
whether a function is actually deterministic.
For that reason,
\salt{} was introduced in \cite{orig}.
In \salt{},
every expression that may assume multiple values
must have set type |Set|.

\section{The translation rules}

The translation method below is an adaption of \cite{orig}.
The version presented here is different
because the languages \cumin{} and \salt{} are more general:
Constructors do not have to be fully applied,
there are more ADTs than |List|, |Bool| and |Pair|,
and the syntax for indexed unions is more general.
As a consequence, one has to keep track of type information,
in contrast to \cite{orig}
where the transformation is purely syntactical.

The translation method is pessimistic insofar
as it transforms every \cumin{} expressions
into a set-typed expressions
even if it is deterministic.
This shortcoming will be partly addressed in Section 4.2.

\subsection{Translating types}

Every \cumin{} expression of type |tau|
is translated to a \salt{} expression of type |set (tytrans tau)|
where |tytrans| inserts |Set| to the right of every |->| arrow (\cref{trans-types}).
\begin{figure}[t]
\begin{align*}
|tytrans Nat| &= |Nat| \\
|tytrans (A tau_1 .. tau_n)| &= |A (tytrans tau_1) .. (tytrans tau_n)| \qquad \text{where |A| is the name of an ADT.} \\
|tytrans alpha| &= |alpha| \qquad \text{where |alpha| is a type variable.} \\
|tytrans (tau' -> tau)| &= |tytrans tau' -> set (tytrans tau)|
\end{align*}
\caption{Translation of types}
\label{trans-types}
\hrulefill
\end{figure}
For example,
a \cumin{} expression |f| of type |(Nat -> Bool) -> Nat| will be translated to
a \salt{} expression of type |Set ((Nat -> Set Bool) -> Set Nat)|.
The reason for the outer |Set| is
that the |f| itself may be nondeterministic,
\ie it might represent multiple functions;
for the |Set| in the argument
that |f| may be given a nondeterministic function as an argument;
and for the remaining |Set|
that |f| may compute more than one natural number.

\subsection{Translating data declarations}

In the same way as types,
we have to translate data type declarations.
Recall that an ADT declaration in \cumin{} looks like this.
> data A alpha_1 .. alpha_m =  C_1 tau_11 tau_12 .. |  C_2 tau_21 tau_22 .. |  ..
Here, |C_1, C_2 ..| are the constructors
and the |tau|'s their argument types.
It will be translated to the following \salt{} ADT declaration.
> data A alpha_1 .. alpha_m =  C_1 (tytrans tau_11) (tytrans tau_12) .. |  C_2 (tytrans tau_21) (tytrans tau_22) .. |  ..

As an example, consider difference lists.
> data DList alpha = DList (List alpha -> List alpha)
This is translated to the following \salt{} declaration.
> data DList alpha = DList (List alpha -> Set (List alpha))

Such higher order data structures are rather rare, however.
Most of the time,
the data declarations will contain no function types
and the translation to \salt{} will look the same.

\subsection{Translating expressions}

How \cumin{} expressions are translated can be seen in \cref{trans-exp}.
The conversion function is denoted by |trans|.
\begin{figure}[t]
\begin{align*}
\trans{|x|} &= |set x| \qquad \text{where |x| is a variable} \\
\trans{|n|} &= |set n| \qquad \text{where |n| is a literal} \\
\trans{|C<:vec rho_m:>!|} &= |set (\x_1 :: tytrans tau'_1 -> .. set (\x_n :: tytrans tau'_n -> C<:vec (tytrans rho_m):> x_1 .. x_n))| \\*
&\qquad\text{for every |data A (vec alpha_m) = .. || C tau_1 .. tau_n || ..| in \cumin{}} \\*
&\qquad\text{and where |tau'_i = tau_i[vec (rho_m/alpha_m)]|.} \\
\trans{|failed<:tau:>!|} &= |set (failed<:tytrans tau:>!)| \\
\trans{|let x :: tau free in e|} &= |unknown<:tytrans tau:>! >>= \x :: tytrans tau -> trans e| \\
\trans{|f<:tau_1,..,tau_n:>!|} &= |f<:tytrans tau_1,..,tytrans tau_n:>| \\
\trans{|let x = e_1 in e_2|} &= |trans e_1 >>= \x :: tau -> trans e_2| \\*
&\qquad \text{where |trans e_1 :: Set tau|.} \\
\trans{|f e|} &= |trans f >>= \f' :: tau_1 -> trans e >>= \e' :: tau_2 -> f' e'| \\*
&\qquad \text{where |trans f :: Set tau_1|, |trans e :: Set tau_2| and |f', e'| are fresh variables.} \\
\trans{|e_1 + e_2|} &= |trans e_1 >>= \x_1 :: Nat -> trans e_2 >>= \x_2 :: Nat -> set (x_1 + x_2)| \\*
&\qquad \text{where |x_1| and |x_2| are fresh variables.} \\
\trans{|e_1 == e_2|} &= |trans e_1 >>= \x_1 :: tau -> trans e_2 >>= \x_2 :: tau -> set (x_1 == x_2| \\*
&\qquad \text{where |trans e_i :: Set tau| and |x_i| are fresh variables.} \\
\trans{|case e of { p_1 -> e_1; .. }|} &= |trans e >>= \x :: tau -> case x of { p_1 -> trans e_1; .. }| \\*
&\qquad \text{where |trans e :: Set tau| and |x| is a fresh variable.}
\end{align*}
\caption{Translation rule for expressions}
\label{trans-exp}
\hrulefill
\end{figure}
As mentioned before,
an expression of type |tau| is translated to one of type |Set (tytrans tau)|.
This is achieved by adding sufficiently many |Set| in the right places
(cf. the first four rules).
|unknown| already has |Set|-type in \salt{},
so it does not need extra |set|-braces.

The other translation rules handle expressions composed of subexpressions.
They generally work by
translating these subexpressions,
\enquote{extracting} the elements using |>>=| and
acting on these.
For example |1 + 1| will be translated to
> set 1 >>= \x :: Nat -> set 1 >>= \y :: Nat -> set (x + y)
Needless to say,
this translation is rather naïve and not very efficient --
it could simply be translated to |{1 + 1}|.
We will address this problem later.

Most of the rules in \cref{trans-exp} are taken from \cite{orig}
with mostly small modifications
because of the differences in syntax and generality of ADTs.
However, the translation of constructors had to be generalized
because they in our version of \cumin{},
they are allowed to be partially applied.
Therefore, they are translated similar to regular \cumin{} functions,
which are discussed in the next section,
namely by wrapping each \enquote{level} in singleton sets.

\subsection{Translating function declarations}

The final step in translating \cumin{} programs to \salt{} programs
are function declarations.
Remember that a function declaration in \cumin{} is given by
> f :: forall alpha_1 .. alpha_m. tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_n = e
where |e| denotes the expression
on the right hand side of the function definition.

Such a function is translated to the following \salt{} function.
> f :: forall alpha_1 .. alpha_m. Set (tytrans (tau_1 -> .. -> tau_n -> tau))
> f = set (\x_1 :: tytrans tau_1 -> set (.. set (\x_n :: tytrans tau_n -> trans e)))
Note that we now have to use explicit lambda abstractions
(which did not even exist in \cumin{})
because each (sub-)function needs to be wrapped in |set|-braces.

\subsection{Examples}

Some example translations can be seen below.\\[.5cm]
\begin{minipage}{.4\textwidth}%
\texths\small%
\begin{code}
id :: forall a. a -> a
id x = x
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}%
\texths\small%
\begin{code}
id :: forall a. Set (a -> Set a)
id = { \x :: a -> { x } }
\end{code}
\end{minipage}
\\[.5cm]
\begin{minipage}{.4\textwidth}%
\texths\small%
\begin{code}
choose :: forall a. a -> a -> a
choose x y = let c :: Bool free in
  case c of { True -> x; False -> y }
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}%
\texths\small%
\begin{code}
choose :: forall a. Set (a -> Set (a -> Set a))
choose = { \x :: a -> { \y :: a ->
  unknown<:Bool:> >>= \c :: Bool ->
  case c of { True -> {x}; False -> {y} } } }
\end{code}
\end{minipage}
\\[.5cm]
\begin{minipage}{.4\textwidth}%
\texths\small%
\begin{code}
length :: forall a. List a -> Nat
length xs = case xs of
  Nil -> 0
  Cons y ys -> 1 + length<:a:> ys
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}%
\texths\small%
\begin{code}
length :: forall a. Set (List a -> Set Nat)
length = {\xs :: List a -> {xs} >>=
  \scrutinee :: List a -> case scrutinee of
    Nil -> {0}
    Cons y ys -> {1} >>= \one :: Nat ->
      (length<:a:> >>= \len :: (List a -> Set Nat) ->
      {ys} >>= \ys' :: List a -> len ys') >>=
      \l :: Nat -> {one + l}
  }
\end{code}
\end{minipage}
\\[.5cm]

\section{Improving the generated \salt{} code}

As one can see in the example programs,
the translated expressions are often unnecessarily set-typed,
so there is a lot of \enquote{plumbing} with |set| and |>>=| required.
However, there are some simple transformations
that can be used to make the \salt{} code much more efficient.

One transformation that is not directly useful
but helps a lot with other simplifications is $\beta$-reduction:
Given an expression of the form |(\x -> e_1) e_2|,
one can turn it into |e_1[e_2/x]|.
However, $\beta$-reducing is not always beneficial:
Substituting the expression |e_2| into |e_1|
can lead to wasteful recomputation
if |x| occurs in |e_1| more than once.
Hence, this simplification should only be used
when the bound variable occurs at most once.\footnote{
There are actually more cases where this is safe,
for example, if the variable occurs only once
in each branch of a case expression.
However, there is still some code being duplicated,
which may increase program size considerably.
To keep things simple, I did not explore that further.}
Note that variable capture on substitution is an issue, as well.
It is addressed in Section 4.3.

Similarly to $\beta$-reduction,
there is $\eta$-reduction:
An expression of the form |\x -> f x| is equivalent to |f|
if |x| does not occur freely in |f|.
In contrast to $\beta$-reduction,
this transformation is always safe and beneficial.
Note that while $\eta$-reduction is not valid for \cumin{} (\cf Section 3.1),
it is allowed in \salt{}
because there is no nondeterminism or call-time choice.

It was mentioned before
that the set type constructor |Set| forms a monad,
in particular, it obeys the \emph{monad laws} listed below.
\begin{enumerate}
\item |({ e } >>= f) ~= (f e)|
\item |(e >>= \x -> { x }) ~= e|
\item |(e >>= f) >>= g ~= e >>= (\x -> f x >>= g)|
\end{enumerate}
The symbol |~=| denotes \emph{semantic equivalence},
which means that the evaluate to the same result,
and is formally defined in \cite{orig}.
For lack of space, I cannot develop this theoretical background,
which is necessary to prove these laws.

\todo[inline]{Use set notation to give more intuition}

The first monad law, viewed as a transformation from left to right,
is extremely useful
for simplifying the translated \salt{} programs.
\cumin{} literals and variables are translated to singleton sets,
which makes this law applicable in many cases.
Afterwards, $\beta$-reduction can be applied as a next step.
As an example, consider the term |1 + 1|.
Its translated version can be simplified using the first monad law twice
and then $\beta$-reducing twice:
\begin{code}
set 1 >>= \x :: Nat -> set 1 >>= \y :: Nat -> set (x + y)
~= (\x :: Nat -> set 1 >>= \y :: Nat -> set (x + y)) 1
~= (\x :: Nat -> (\y :: Nat -> set (x + y)) 1) 1
~= (\y :: Nat -> set (1 + y)) 1
~= set (1 + 1)
\end{code}

The second monad law is not very useful,
it can only be applied
in case of unnecessary let-bindings like
|let x = e in x|.

The utility of the third monad law is not immediately obvious.
However, it can be used to \enquote{re-associate} |>>=|-bindings,
thus enabling the application of the first rule in some cases.
For instance, consider the expression |(x >>= \y -> { f }) >>= \g -> g y|.
At first sight, neither the first nor the second law can be applied.
The third monad law allows as to transform this into
|x >>= \y -> ({ f } >>= \g -> g y)|.
Now, the first monad law is applicable and yields
|x >>= \y -> f y| after $\beta$-reduction.
Using $\eta$-equivalence, we arrive at |x >>= f|, as desired.

This is not a hypothetical scenario but happens
in real translated \salt{} programs.
For instance, consider the \cumin{} expression
|Cons<:Nat:> coin Nil<:Nat:>|.
Translating this to \salt{} and applying the first monad law yields:
\begin{code}
trans (Cons<:Nat:> coin Nil<:Nat:>!)
~= (coin >>= \c :: Nat -> { \xs :: List Nat -> { Cons<:Nat:> c xs } })
  >>= \f :: (List Nat -> Set (List Nat)) -> f Nil<:Nat:>
\end{code}
Applying the third monad enables the first monad law and $\beta$-reduction:
\begin{code}
coin >>= \c :: Nat ->
  ({ \xs :: List Nat -> { Cons<:Nat:> c xs } }
  >>= \f :: (List Nat -> Set (List Nat)) -> f Nil<:Nat:>!)
~= coin >>= \c :: Nat ->
  (\xs :: List Nat -> { Cons<:Nat:> c xs }) Nil<:Nat:>
~= coin >>= \c :: Nat -> { Cons<:Nat:> c Nil<:Nat:> }
\end{code}
As a simplification, one can limit oneself
to only ever applying the third monad law from left to right.
This is because the first monad law can be used much more often
than the second one, and it benefits only from this direction.
In the example programs I looked at,
the other direction was never beneficial.

As a larger example,
let us look at how the simplifications transform the prelude function |length|.
The original version is on the left,
the simplified one on the right.\\[0.5em]
\begin{minipage}{.5\textwidth}%
\texths\small%
\begin{code}
length :: forall a. Set (List a -> Set Nat)
length = {\xs :: List a -> {xs} >>=
  \scrutinee :: List a -> case scrutinee of
    Nil -> {0}
    Cons y ys -> {1} >>= \one :: Nat ->
      (length<:a:> >>= \len :: (List a -> Set Nat) ->
      {ys} >>= \ys' :: List a -> len ys') >>=
      \l :: Nat -> {one + l}
  }
\end{code}
\end{minipage}
\begin{minipage}{.5\textwidth}%
\texths\small%
\begin{code}
length :: forall a. Set (List a -> Set Nat)
length = { \xs :: List a -> case xs of
  Nil -> 0
  Cons y ys -> length<:a:> >>=
    \length' :: (List a -> Set Nat) ->
    length' ys >>= \l :: Nat -> {1 + l} }
\end{code}
\end{minipage}
\\[.5cm]
This is a considerable improvement.
There is only one thing that could be done better in a manual translation,
by exploiting the fact that the function is in fact deterministic,
which is discussed in Section 5.4 by means of the same example.

\section{Implementation}

The implementation is relatively close to the translation
and simplification rules described above.
The program recursively traverses the syntax tree and applies them.
I will now explain some implementation details.
An overview of the implementation is given afterwards.

While the translation given in \cite{orig} is purely syntactical,
the adapted version presented here requires type information.
For example, let bindings do not have a type annotation
but they are translated to lambda abstractions, which need one.
As a consequence, one has to keep track of the types of bound variables
while traversing the syntax tree.
Another problem is fresh variables and capture avoidance
which was briefly discussed in Section 2.5.1.
Fresh variables could be generated as before, by appending a unique number.
Variable capture is a real problem, however:
$\beta$-reducing |(\z -> (\y -> z)) (\x -> y)|
by blind substitution
yields |\y -> (\x -> y)| which is incorrect,
since the variable |y| is not free anymore.
This could be solved
by examining the variables of the substituted expression
and renaming them, if necessary.
This is rather complicated and relatively hard to get right.

I chose the following different solution:
I used a nameless representation of terms,
where variables are not identified by names
but by \enquote{how many levels up the syntax tree they were bound}.
This is made precise below.

\subsection{Nameless representation}

To handle bound variables, I used the \verb!bound! library\footnote{
\url{http://hackage.haskell.org/package/bound}
} by Edward Kmett.
It has the following variable type:
> data Var b a = B b | F a
|B b| represents a variable bound directly
by the next binding up the syntax tree.
|F a| represents a free variable,
it is not directly bound by the next parent binding.
But it may be bound at higher levels in the syntax tree.

For illustration purposes, consider the following expression type:
> data Exp v = Var v | Lam (Scope () Exp v)
|v| is the variable type of the expression.
|Scope| is provided by the \verb!bound! library and represents a binder.
The general form is
> data Scope b f a = Scope (f (Var b (f a)))
where |b| represents additional information for bound variables,
in this case none, \ie |()|;
|f| represents the expression type
and |a| the type of free variables,
not bound in this scope;
and |a| represents the type of free variables in the binder.
For example, the expression |\x -> \y -> x| would be represented as
> Lam (Scope (Lam (Scope (Var (F (Var (B ())))))))
|F| \enquote{lifts} the bound variable |B ()| one level up,
so it is bound by the outer lambda instead of the inner one.
For lack of space, I cannot give a longer introduction to the library.
But I want to highlight some of its advantages.

First of all, variable capture is not a problem anymore,
and substitution is for the most part handled in the library.
Additionally, there is a lot more type safety
than in a representation with names:
For example, a term without free variables can be given the type
|Exp Void| where |Void| is an empty type.
In fact, this is what I do for \salt{} functions in the program,
since they have to be closed terms.
(Calling top-level functions is not represented as a free variable.)
Furthermore, lots of mistakes when handling variables
can be caught at compile time.
The reason is that
blunders like forgetting a binder lead to type errors in the Haskell code
because the variable types do not match up.

\subsection{General approach}

I implemented  the translation method as a program called \verb!cumin2salt!.
On execution, it is passed a \cumin{} program to translate,
and whether the result should be simplified.
My implementation proceeds as follows.

The \cumin{} program is parsed and
type checked.
If there were no errors, it is translated to the nameless representation.
This one, in turn, is transformed to a nameless \salt{} representation,
following the translation rules.
If desired by the user,
the simplifications $\beta$-reduction, $\eta$-reduction and the monad laws
are used to improve the generated \salt{} code.
This nameless \salt{} AST is then translated to a regular \salt{} AST.
This is done by giving names to the bound variables.
To guarantee these are unique, each one gets a unique number.
Note that only one renaming pass over the AST is necessary,
everything before is handled by the nameless representation.
Also, the original variable names are still retained if possible
to make the output more readable.
Finally, this \salt{} AST is pretty-printed and written to a file.

\subsection{Command Line Interface}

The command line arguments to the program look like this:
\begin{verbatim}
cumin2salt INPUT [-o OUTPUT] [-s|--simplify] [--with-prelude]
\end{verbatim}
The program is given a \cumin{} input file name and, possibly,
a \salt{} output file name (default: \verb!Out.salt!).
If the \salt{} output should be simplified,
one should pass the option \verb!-s!.
The switch \verb!--with-prelude! controls
whether the prelude functions should be included in the output.
Normally, the translated prelude functions need not be included,
as they are provided by the alternative \salt{} prelude (cf. Chapter 2.4).
Of course, \verb!--help! can be used to show a help text.

\subsection{Example}

As an example,
consider the following automatic translation of the |length| function.
\begin{code}
length :: forall a. Set (List a -> Set Nat)
length = {\xxs86 :: List a -> case xxs86 of
    Nil -> {0}
    Cons x87 xs88 -> length<:a:> >>= (\arg89 :: (List a
                                         -> Set Nat) -> arg89 xs88 >>=
      (\primOpArg90 :: Nat -> {1 + primOpArg90}))}
\end{code}
As can be seen, numbers are appended to variable names
to make them unique.
Apart from that, this output matches the manual translation seen above.

\subsection{Correctness}

To ensure correctness of the translation program,
I took the following measures:
First, type checking \cumin{} and \salt{} programs
is a very useful consistency check.
After every simplification, it is checked that the type did not change.
Additionally, after the whole translation,
it is checked that the \salt{} functions have the right types,
namely that a \cumin{} function of type |tau|
is translated to a \salt{} function of type |Set (tytrans tau)|.
This catches a large class of bugs.

Testing is still necessary, of course.
The implementation of denotational semantics for \cumin{} and \salt{}
by Fabian Thorand is his bachelor thesis provides a good way to do this.
A \cumin{} expression in the context of some program
must have the same semantics
as the translated expression in context of the translated program.
This procedure is executed for several test programs and expressions.

Together, type checking and testing using the denotational semantics
strengthen the claim that the translation preserves the semantics
and thus works as intended.
