\chapter{Translating \cumin{} to \salt{}}

\cumin{} is convenient
because non-determinism is implicit.
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
It is pessimistic insofar
as it transforms every \cumin{} expressions
into a set-typed expressions
even if it is deterministic.
This shortcoming will be partly addressed in the next chapter.

\subsection{Translating types}

Every \cumin{} expression of type |tau|
is translated to a \salt{} expression of type |set (tytrans tau)|
where |tytrans| inserts |Set| to the right of every |->|.
Formally:
\begin{align*}
|tytrans Nat| &= |Nat| \\
|tytrans A| &= |A| \qquad \text{where |A| is the name of an ADT.} \\
|tytrans alpha| &= |alpha| \qquad \text{where |alpha| is a type variable.} \\
|tytrans (tau' -> tau)| &= |tytrans tau' -> set (tytrans tau)| \\
\end{align*}

For example,
a \cumin{} expression |f| of type |(Nat -> Bool) -> Nat| will be translated to
a \salt{} expression of type |Set ((Nat -> Set Bool) -> Set Nat)|.
The reason for the outer |Set| is
that the |f| itself may be non-deterministic,
i.e. it might represent multiple functions;
for the |Set| in the argument
that |f| may be given a non-deterministic function as an argument;
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

How \cumin{} expressions are translated can be seen below.
|trans| denotes the conversion function.
\begin{align*}
\trans{|x|} &= |set x| \qquad \text{where |x| is a variable} \\
\trans{|n|} &= |set n| \qquad \text{where |n| is a literal} \\
\trans{|C<:vec rho_m:>!|} &= |set (\x_1 :: tytrans tau'_1 -> .. set (\x_n :: tytrans tau'_n -> C<:vec (tytrans rho_m):> x_1 .. x_n))| \\*
&\qquad\text{for every |data A (vec alpha_m) = .. || C tau_1 .. tau_n || ..| in \cumin{}} \\*
&\qquad\text{and where |tau'_i = tau_i[vec (rho_m/alpha_m)]|.} \\
\trans{|failed<:tau:>!|} &= |set (failed<:tytrans tau:>!)| \\
\trans{|unknown<:tau:>!|} &= |unknown<:tytrans tau:>| \\
\trans{|f<:tau_1,..,tau_n:>!|} &= |f<:tytrans tau_1,..,tytrans tau_n:>| \\
\trans{|let x = e_1 in e_2|} &= |trans e_1 >>= \x :: tau -> trans e_2| \\*
&\qquad \text{where |trans e_1 :: Set tau|.} \\
\trans{|f e|} &= |trans f >>= \f' :: tau_1 -> trans e >>= \e' :: tau_2 -> set (f' e')| \\*
&\qquad \text{where |trans f :: Set tau_1|, |trans e :: Set tau_2| and |f', e'| are fresh variables.} \\
\trans{|e_1 + e_2|} &= |trans e_1 >>= \x_1 :: Nat -> trans e_2 >>= \x_2 :: Nat -> set (x_1 + x_2)| \\*
&\qquad \text{where |x_1| and |x_2| are fresh variables.} \\
\trans{|e_1 == e_2|} &= |trans e_1 >>= \x_1 :: tau_1 -> trans e_2 >>= \x_2 :: tau_2 -> set (x_1 == x_2| \\*
&\qquad \text{where |trans e_i :: Set tau_i| and |x_i| are fresh variables.} \\
\trans{|case e of { p_1 -> e_1; .. }|} &= |trans e >>= \x :: tau -> case x of { p_1 -> trans e_1; .. }| \\*
&\qquad \text{where |trans e :: Set tau| and |x| is a fresh variable.} \\
\end{align*}

As discussed above,
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

\subsection{Translating function declarations}

The final step in translating \cumin{} programs to \salt{} programs
are function declarations.
Remember that a function declaration in \cumin{} is given by
> f :: forall alpha_1 .. alpha_m. tau_1 -> .. -> tau_n -> tau
> f x_1 .. x_l = e
where |e| denotes the expression
on the right hand side of the function definition.

Such a function is translated to the following \salt{} function.
> f :: forall alpha_1 .. alpha_m. Set (tytrans (tau_1 -> .. -> tau_n -> tau))
> f = set (\x_1 :: tytrans tau_1 -> set (.. set (\x_l :: tytrans tau_l -> trans e)))
Note that we now have to use explicit |\|-abstractions
(which did not even exist in \cumin{})
because each (sub-)function needs to be wrapped in |set|-braces.

\subsection{Examples}

Some example translations can be seen below.\\[.5cm]
\begin{minipage}{.4\textwidth}%
\texths\small%
\begin{code}
id :: forall a. a -> a
id a = a
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}%
\texths\small%
\begin{code}
id :: forall a. Set (a -> Set a)
id = { \a :: a -> { a } }
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
length = { \xs :: List a -> case xs of
  Nil -> 0
  Cons y ys -> { 1 } >>= \i :: Nat ->
    length<:a:> >>= \length' :: (List a -> Set Nat) ->
    { ys } >>= \ys'->
    length' ys' >>= \l :: Nat -> { i + l } }
\end{code}
\end{minipage}
\\[.5cm]

\section{Improving the generated \salt{} code}

As we have seen above,
the translation rules are relatively naïve.
Translated expressions are often unnecessarily set-typed,
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

It was mentioned before
that the set type constructor |Set| forms a monad,
in particular, it obeys the \emph{monad laws} listed below.
The symbol |~=| denotes semantical equivalence.
\begin{enumerate}
\item |({ e } >>= f) ~= (f e)|
\item |(e >>= \x -> { x }) ~= e|
\item |(e >>= f >>= g) ~= (e >>= \x -> f x >>= g)|
\end{enumerate}

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
For instance, consider the expression |x >>= \y -> { f } >>= \g -> g y|.
At first, neither the first nor the second law can be applied
since |>>=| associates to the left.
(It is implicitly parenthesized like this:
|(x >>= \y -> { f }) >>= \g -> g y|.)
The third monad law allows as to transform this into
|x >>= \y -> ({ f } >>= \g -> g y)|.
Now, the first monad law is applicable and yields
|x >>= \y -> f y| after $\beta$-reduction, as desired.

This is not a hypothetical scenario but happens
in real translated \salt{} programs.
For instance, consider the \cumin{} expression
|Cons<:Nat:> coin Nil<:Nat:>|.
Translating this to \salt{} and applying the first monad law yields:
\begin{code}
trans (Cons<:Nat:> coin Nil<:Nat:>!)
~= coin >>= \c :: Nat -> { \xs :: List Nat -> { Cons<:Nat:> c xs } }
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

As a larger example,
let us see at how the simplifications transforms the prelude function |length|.
The original version is on the left,
the simplified one on the right.\\[0.5em]
\begin{minipage}{.5\textwidth}%
\texths\small%
\begin{code}
length :: forall a. Set (List a -> Set Nat)
length = { \xs :: List a -> case xs of
  Nil -> 0
  Cons y ys -> { 1 } >>= \i :: Nat ->
    length<:a:> >>= \length' :: (List a -> Set Nat) ->
    { ys } >>= \ys'->
    length' ys' >>= \l :: Nat -> { i + l } }
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
There is only one thing that could be done better.
A smart compiler could recognize
that the |length| function is in fact deterministic.
It could thus generate the following code:
\begin{code}
length' :: forall a. List a -> Nat
length' = \xs :: List a -> case xs of
  Nil -> 0
  Cons y ys -> 1 + length'<:a:> ys

length :: forall a. Set (List a -> Set Nat)
length = { \xs :: List a -> { length'<:a:> xs } }
\end{code}
However, it is not entirely clear
how a compiler might arrive at this solution
and the complexity would be beyond the scope of a bachelor thesis.
The current simplifications produce good results,
and the chance for small improvements does not justify the large additional effort.
