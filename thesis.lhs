\documentclass[11pt,a4paper,abstract=on]{scrreprt}


\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[english]{babel}
\usepackage{csquotes}

\usepackage{lmodern}
\usepackage{microtype}
\usepackage{setspace}

\usepackage{todonotes}
\usepackage{bussproofs}

\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsthm}

\usepackage{hyperref}

\usepackage[backend=biber]{biblatex}

\usepackage{listings}

%include format.fmt

%include commands.lhs

%Configuration:

\allowdisplaybreaks[1]

\newtheorem{definition}{Definition}

\bibliography{thesis}

\begin{document}

\begin{titlepage}
\begin{center}
\textsc{\Large Rheinische Friedrich-Wilhelms-Universität Bonn} \\
\vfill
\textsc{\LARGE Bachelor Thesis}\\
\vfill
\rule{\linewidth}{1pt}
\begin{spacing}{1.2}
  \Huge
  Implementing an Operational Semantics and Nondeterminism Analysis
  for a Functional-Logic Language \\[-0.3cm]
\end{spacing}
\rule{\linewidth}{1pt}
\vfill
\begin{spacing}{1.2}
  \LARGE
  \textbf{Fabian Moritz Frank Zaiser} \\
  Student number: XXXXXX \\
  STREET NUMBER \\
  D-53121 Bonn
\end{spacing}
\vfill
\textit{\Large \today} \\
\vfill
{\Large
Supervisor: Jun.-Prof.\ Dr.\ rer.\ nat.\ habil.\ Janis Voigtländer
} \\
\vfill
\begin{spacing}{1.2}
  \Large
  Institute for Computer Science, Department III \\
  Römerstraße 164 \\
  D-53117 Bonn
\end{spacing}
\end{center}
\end{titlepage}

\begin{abstract}
Functional-logic languages like Curry aim
to combine the strength of both functional and logic languages.
In order to establish free theorems for such languages,
the authors of \cite{orig} have focused their attention
on a language fragment they call \emph{\cumin{}},
which can be translated to another language called \emph{\salt{}}
that makes logic features like non-determinism more explicit.

The aim of this thesis is
to give a more detailed exposition of the two languages
and to document an implementation
of an operational semantics for \cumin{} and the translation to \salt{}.
As the translation described in the paper is rather naïve
in that it assumes everything to be non-deterministic
and as a consequence,
code that does not use logic features is compiled to a cumbersome result.
I explored ways to reduce the amount of unnecessary non-determinism
in the generated SaLT code.
\end{abstract}

\tableofcontents

%include 1-introduction.lhs

%include 2-preliminaries.lhs

%include 3-operational.lhs

%include 4-translation.lhs

%include 5-analysis.lhs

%include 6-conclusion.lhs

\printbibliography

\end{document}
