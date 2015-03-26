\documentclass[11pt,a4paper,headings]{scrbook}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[english]{babel}
\usepackage{csquotes}

\usepackage{lmodern}
\usepackage{microtype}
\usepackage{setspace}
\usepackage[top=3cm,bottom=3cm,inner=3cm,outer=2cm]{geometry}

\usepackage[Lenny]{fncychap}
\usepackage[headsepline]{scrlayer-scrpage}

\usepackage{bussproofs}
\usepackage{tikz}
\usepackage{tikz-qtree}
\usepackage{tabularx}
\usepackage{ltablex}

\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsthm}

\usepackage{hyperref}
\usepackage{cleveref}

\usepackage[backend=biber]{biblatex}

\usepackage{listings}

%include format.fmt

%include commands.lhs

%Configuration:

\allowdisplaybreaks[1]

\newtheorem{definition}{Definition}

\hypersetup{
  pdftitle    = {Implementating an Operational Semantics and
                 Nondeterminism Analysis for a Functional-Logic Language},
  pdfauthor   = {Fabian Zaiser},
  pdfkeywords = {CuMin,
                 Curry,
                 SaLT,
                 Functional-Logic Programming,
                 nondeterminism,
                 operational semantics},
}

\bibliography{thesis}

\begin{document}

\frontmatter

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

\chapter*{Eigenständigkeitserklärung}

Hiermit erkläre ich, Fabian Moritz Frank Zaiser,
dass ich die vorliegende Bachelorarbeit selbstständig verfasst
und keine anderen als die angegebenen Quellen und Hilfsmittel benutzt,
sowie Zitate kenntlich gemacht habe.

\vspace{3cm}

\begin{tabular}{lp{2em}l}
 \hspace{3cm} && \hspace{6cm} \\ \hline
 Ort, Datum && Unterschrift \\
\end{tabular}

\cleardoublepage

\chapter*{Abstract}
Functional-logic languages like Curry aim
to combine the strengths of both functional and logic languages.
In order to establish free theorems for such languages,
the authors of \cite{orig} have focused their attention
on a sublanguage they call \emph{\cumin{}},
which can be translated to another language called \emph{\salt{}}
where logic features like nondeterminism are more explicit.

In this thesis, I will give a detailed exposition of the two languages.
Moreover, I will document
the implementation of an operational semantics for \cumin{}
and of a translation algorithm
that transforms \cumin{} programs into equivalent \salt{} programs.
I will describe how the generated \salt{} code can be simplified
and how it can be used to analyze
the nondeterminism in the original \cumin{} program.

\tableofcontents

\mainmatter

%include 1-introduction.lhs

%include 2-preliminaries.lhs

%include 3-operational.lhs

%include 4-translation.lhs

%include 5-analysis.lhs

%include 6-conclusion.lhs

\printbibliography

\end{document}
