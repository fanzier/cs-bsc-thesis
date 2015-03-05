\chapter{Introduction}

In the field of declarative programming languages,
there are two important paradigms.
One the one hand,
functional programming languages like \emph{Haskell}
are based on the lambda calculus
and commonly include features like
first-class functions,
algebraic data types,
and powerful typing systems.
On the other hand,
logic programming languages like \emph{Prolog}
are based on first-order logic
and allow
computing with partial information,
constraint solving,
and nondeterministic search for solutions.

The declarative programming language \emph{Curry} aims
to combine the most important features of both paradigms in one language.
Curry is based on (a subset of) Haskell
but integrates logic variables and non-deterministic search.
This functional-logic language is well-known and actively researched,
so it makes sense to use it as an introduction to this paradigm.

Afterwards,
I will describe the functional-logic language \cumin{} (Curry Minor),
and \salt{} (Set and Lambda Terms),
both of which were introduced in \cite{orig}.
\cumin{} is a sublanguage of Curry including its characteristic features
but with fewer syntactic constructs,
which simplifies the study of the language.
\salt{} is essentially a lambda-calculus
where, in contrast to \cumin{}, nondeterminism is made explicit
using an abstract set type.
It behaves more like a functional language
and makes it easier, for example,
to derive free theorems%
\footnote{theorems about a function
that can be derived solely from its type signature},
which was the original motivation
to introduce these two languages in \cite{orig}.

In the later sections of this chapter,
I present an example-based overview of these languages.
A more formal description can be found in Chapter 2.
But first, let me give a brief introduction to Hakell,
for one thing because it is the language that Curry is built upon,
for another thing because the implementation part of this thesis
was carried out in Haskell.

\section{Haskell}

Haskell is a purely functional, statically typed, lazy language.
This means
that Haskell functions are more like mathematical functions
than procedures in imperative languages,
in that they always produce the same ouput for the same input,
and side-effects are restricted.
Every expression is typed and the type checker ensures
that the types match up,
thus catching possible bugs at compile time.
Evaluation of terms is delayed by default
until the value is needed,
which for example allows the use of infinite data structures.

\subsection{Functions}

A function definition in Haskell consists of
an (optional) type signature
and one or more defining equations.
The following examples should illustrate the concept.

> double :: Int -> Int
> double x = 2 * x
>
> factorial :: Int -> Int
> factorial 0 = 1
> factorial n = n * factorial (n - 1)
>
> min :: Int -> Int -> Int
> min x y = if x < y then x else y

One can look at |min| as a function
that takes two arguments of type |Int| and returns an integer.
But actually,
|min| is a function that takes one argument of type |Int|
and returns a function of type |Int -> Int|.
This makes |min| a \emph{curried} function.
It becomes more apparent when |min| is written
with an explicit lambda abstraction.
> min :: Int -> (Int -> Int)
> min x = \y -> if x < y then x else y
One can now use |min 0 :: Int -> Int| as a cut-off function
that returns its argument if it is negative and otherwise returns 0.

Functions can also take other functions as their arguments.
In this case, they are called \emph{higher order functions}.
An example is the following.
> applyTwice :: (Int -> Int) -> Int -> Int
> applyTwice f x = f (f x)
Applying this function to |double| results in
> quadruple :: Int -> Int
> quadruple = applyTwice double
which applies |double| to its argument twice,
i.e. multiplies its argument by four.

\subsection{Polymorphism}

Actually, it is not necessary for |applyTwice|
to have its type specialized to |Int|.
It should work for any type.
Indeed, Haskell allows us to write
> applyTwice :: (a -> a) -> a -> a
|a| is a type variable and can be instantiated with any type.
For example, when using this function with |double|,
|a| will be instantiated to type |Int|
in order to match the type of |double|.

Polymorphic functions are very common in Haskell.
Another simple example is the identity function.
> id :: a -> a
> id x = x
As a matter of fact,
it is essentially the only function with this type signature.
(This is an example of free theorems, mentioned earlier.)

Another very common example is function composition.
> (.) :: (b -> c) -> (a -> b) -> a -> c
> (f . g) x = f (g x)
|(.)| is a higher-order binary operator
that composes its two function arguments.
Using it, one can write
> applyTwice f = f . f
because |applyTwice| simply composes the given function with itself.

\subsection{Algebraic Data Types}

Non-primitive data types in Haskell
take the form of \emph{algebraic data types (ADTs)}.
They are defined by giving a name to the new type
and listing all its constructors for that type,
separated by vertical bars.
Each constructor has a name and takes a number of arguments,
the types of which have to be specified.
> data Bool = False | True
> data IntTree = Leaf Int | Node Tree Tree
The first data type has two nullary constructors,
|False| and |True|.
These constitute its only values.
The second data type specifies a binary tree
whose leafs are annotated with an integer.
Its values include for instance |Leaf 0|
or | Node (Leaf 10) (Node (Leaf 7) (Leaf 2))|.

Data types can also be polymorphic.
To this end, type variables can be added after the name of the ADT
and the types on the right-hand side can use them. Example:
> data Tree a = Leaf a | Node (Tree a) (Tree a)
Using this definition, |Tree Int| is equivalent to |IntTree| from above.
Singly-linked lists are also represented as ADTs:
> data List a = Nil | Cons a (List a)
Here, |Nil| represents the empty list
and |Cons| prepends one element to another list.
As an example, the list 1, 2, 3 is represented
by |Cons 1 (Cons 2 (Cons 3 Nil)) :: List Int|.
In Haskell,
there is special syntax for lists:
|List a| is written |[a]|, |Nil| is |[]| and |Cons x xs| is |x:xs|.

\subsection{Pattern Matching}

Constructors of algebraic data types give a way to create values of ADTs.
How can one find out which constructor a value was built with
and what its arguments are?
This is done by pattern matching.
In the simplest form,
this is achieved with a |case| expression:
> map :: (a -> b) -> List a -> List b
> map f list = case list of
>   Nil -> Nil
>   Cons x rest -> Cons (f x) (map f rest)
|map| applies a function to every element of a list.
It inspects the list by |case| splitting over its value.
If it is the empty list |Nil|,
the result is also |Nil|.
If it begins with an element |x|,
the function is applied to |x|
and recursively to the rest of the list.
Haskell has special syntactic sugar
for pattern matches on function arguments,
which allows |map| to be written like this:
> map _ Nil = Nil
> map f (Cons x rest) = Cons (f x) (map f rest)

\subsection{Lazy Evaluation}

As mentioned above,
Haskell's evaluation strategy is lazy.
That means it evaluates expressions only as much as is necessary.
Broadly speaking,
the only way to evaluate something is
by pattern matching on it.\footnote{
|seq| is an exception, of course,
but this goes beyond the scope of this overview.}
Consider the following program.
> zeros :: List Int
> zeros = Cons 0 zeros
>
> take :: Int -> List a -> List a
> take 0 _ = Nil
> take n (Cons x xs) = Cons x (take (n - 1) xs)
It defines |zeros|, an infinite list of zeros,
and |take|, a function returning the the first elements of a list.
For instance,
> take 2 (Cons 1 (Cons 2 (Cons 3 Nil))) == Cons 1 (Cons 2 Nil)
But also |take 2 zeros| terminates in finite time
and works as expected because of lazy evaluation
> take 2 zeros
> == take 2 (Cons 0 zeros)
> == Cons 0 (take 1 zeros)
> == Cons 0 (Cons 0 (take 0 zeros)
> == Cons 0 (Cons 0 Nil)
Since |take| does not require the value of |zeros| in the last step
because |take 0| does not pattern match on the list,
therefore |zeros| is not evaluated further
and the program does not run into an infinite loop.

\todo[inline]{Include type classes?}

\section{Curry}
