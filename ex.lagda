\begin{code}[hide]

-- {-# OPTIONS --omega-in-omega --type-in-type #-}

module ex where

data aℕ : Set where
  zero' : aℕ

variable
  A : Set
  D : Set
  stuff : Set

definition-body = aℕ

T = aℕ → aℕ
L = aℕ
E = aℕ
C = aℕ

proof : L
proof = zero'

corollaryStuff = aℕ

proofNeedingLemma : aℕ → aℕ → aℕ
proofNeedingLemma x = λ x₁ → zero'

\end{code}

\subsubsection{Agda Programming}

To give a brief overview of the syntax Agda uses for judgements, namely \term{T}
: \term{Set} means \term{T} is a type, \term{t} : \term{T} means a term \term{t}
has type \term{T}, and \term{t} = \term{t'} means \term{t} is defined to be
judgmentally equal to \term{t'}. Once one has made this equality judgement, Agda
can normalize the definitionally equal terms to the same normal form in
downstream programs. Let's compare it these judgements to those keywords ubiquitous in
mathematics, and show how those are represented in Agda directly below.

\begin{figure}
\centering
\begin{minipage}[t]{.3\textwidth}
\vspace{2cm}
\begin{itemize}
\item Axiom
\item Definition
\item Lemma
\item Theorem
\item Proof
\item Corollary
\item Example
\end{itemize}
\end{minipage}%
\begin{minipage}[t]{.55\textwidth}
\begin{code}
postulate   -- Axiom
  axiom : A

definition : stuff → Set --Definition
definition s = definition-body

theorem : T     -- Theorem Statement
theorem = proofNeedingLemma lemma -- Proof
  where
    lemma : L     -- Lemma Statement
    lemma = proof

corollary : corollaryStuff → C
corollary coro-term = theorem coro-term

example : E     -- Example Statement
example = proof
\end{code}
\end{minipage}
\caption{Mathematical Assertions and Agda Judgements} \label{fig:O1}
\end{figure}

Formation rules, are given by the first line of the data declaration, followed
by some number of constructors which correspond to the introduction forms of the
type being defined. Therefore, to define a type for Booleans, $𝔹$, we present
these rules both in the proof theoretic and Agda syntax. We note that the
context $\Gamma$ is not present in Agda.

\begin{minipage}[t]{.4\textwidth}
\vspace{3mm}
\[
  \begin{prooftree}
    \infer1[]{ \vdash 𝔹 : {\rm type}}
  \end{prooftree}
\]
\[
  \begin{prooftree}
    \infer1[]{ \Gamma \vdash true : 𝔹  }
  \end{prooftree}
  \quad \quad
  \begin{prooftree}
    \infer1[]{ \Gamma \vdash false : 𝔹  }
  \end{prooftree}
\]
\end{minipage}
\begin{minipage}[t]{.3\textwidth}
\begin{code}
data 𝔹 : Set where -- formation rule
  true  : 𝔹 -- introduction rule
  false : 𝔹
\end{code}
\end{minipage}

As the elimination forms are deriveable from the introduction rules, the
computation rules can then be extracted by via the harmonious relationship
between the introduction and elmination forms \cite{pfenningHar}. Agda's pattern
matching is equivalent to the deriveable dependently typed elimination forms
\cite{coqPat}, and one can simply pattern match on a boolean, producing multiple
lines for each constructor of the variable's type, to extract the classic
recursion principle for Booleans. Below we see the boolean elimination form
along with its computation rules. We don't include the premises of the eqaulity
rules as rules because they redundantly use the same premises as the typing
judgment.

\begin{minipage}[t]{.4\textwidth}
\[
  \begin{prooftree}
    \hypo{̌\Gamma \vdash A : {\rm type} }
    \hypo{\Gamma \vdash b : 𝔹 }
    \hypo{\Gamma \vdash a1 : A}
    \hypo{\Gamma \vdash a2 : A }
    \infer4[]{\Gamma \vdash boolrec\{a1;a2\}(b) : A }
  \end{prooftree}
\]
$$\Gamma \vdash boolrec\{a1;a2\}(true) \equiv a1 : A$$
$$\Gamma \vdash boolrec\{a1;a2\}(false) \equiv a2 : A$$
\end{minipage}
\hfill
\begin{minipage}[t]{.5\textwidth}
\begin{code}
if_then_else_ :
  {A : Set} → 𝔹 → A → A → A
if true then a1 else a2 = a1
if false then a1 else a2 = a2
\end{code}
\end{minipage}

When using Agda one is working interactively via holes in the emacs mode.

Glossing over many details, we show a sample of code in the proof development
state prior to pattern matching on \codeword{b}, we have a hole, \codeword{{ b
}0}. The proof state is displayed to the right. It shows both the current
context with \codeword{A, b, a1, a2}, the goal which is something of type
\codeword{A}, and what we have, \codeword{B}, represents the type of the
variable in the hole.

\hfill
\begin{minipage}[t]{.4\textwidth}
\begin{verbatim}
if_then_else_ :
  {A : Set} → B → A → A → A
if b then a1 else a2 = { b }0
\end{verbatim}
\end{minipage}
\hfill
\begin{minipage}[t]{.5\textwidth}
\begin{verbatim}
Goal: A
Have: B
———————————————
a2 : A
a1 : A
b  : B
A  : Set   (not in scope)
\end{verbatim}
\end{minipage}

The interactivity is performed via emacs commands, and every time one updates
the hole with a new term, we can immediately view the next goal with an updated
context. The underscore in \term{if_then_else_} denotes the placement of the
arguement, as Agda allows mixfix operations. Agda allows for more nuanced
syntacic features out of the box than most programming languages provide, like
unicode. This is interesting from the \emph{concrete syntax} perspective as the
arguement placement and symbolic expressiveness makes Agda's syntax feel more
familiar to the mathematician. We also observe the use of parametric
polymorphism, namely, that we can extract a member of some arbtitrary type
\term{A} from a boolean value given two members of \term{A}.

This polymorphism allows one to implement simple programs like \term{~} and more
interestingly, \term{functionalNegation} where one can use functions as
arguements. \term{functionalNegation} is a functional, or higher order
functions, which take functions as arguements and return functions. We also
notice in \term{functionalNegation} that one can work directly with lambda's to
ensure the correct return type.

\begin{code}
~ : 𝔹 → 𝔹
~ b = if b then false else true

functionalNegation : 𝔹 → (𝔹 → 𝔹) → (𝔹 → 𝔹)
functionalNegation b f = if b then f else λ b' → f (~ b')
\end{code}

This simple example leads us to one of the domains our subsequent grammars will
describe, arithmetic (see \ref{npf}). We show how to inductively define natural numbers in Agda,
with the formation and introduction rules included beside for contrast.

\begin{minipage}[t]{.4\textwidth}
\vspace{3mm}
\[
  \begin{prooftree}
    \infer1[]{ \vdash ℕ : {\rm type}}
  \end{prooftree}
\]
\[
  \begin{prooftree}
    \infer1[]{ \Gamma \vdash 0 : ℕ  }
  \end{prooftree}
  \quad \quad
  \begin{prooftree}
    \hypo{\Gamma \vdash n : ℕ}
    \infer1[]{ \Gamma \vdash (suc\ n) : ℕ  }
  \end{prooftree}
\]
\end{minipage}
\begin{minipage}[t]{.3\textwidth}
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}
\end{minipage}

This is our first observation of a recursive type, whereby pattern matching over
$ℕ$ allows one to use an induction hypothesis over the subtree and gurantee
termination when making recurive calls on the function being defined. We can
define a recursion principle for $ℕ$, which essentially gives one the power to
build iterators. Again, we include the elimination and equality
rules for syntactic juxtaposition.

\[
  \begin{prooftree}
    \hypo{̌\Gamma \vdash X : {\rm type} }
    \hypo{\Gamma \vdash n : ℕ }
    \hypo{\Gamma \vdash e₀ : X}
    \hypo{\Gamma, x : ℕ, y : X \vdash e₁ : X }
    \infer4[]{\Gamma \vdash natrec\{e\;x.y.e₁\}(n) : X }
  \end{prooftree}
\]
$$\Gamma \vdash natrec\{e₀;x.y.e₁\}(n) \equiv e₀ : X$$
$$\Gamma \vdash natrec\{e₀;x.y.e₁\}(suc\ n) \equiv e₁[x := n,y := natrec\{e₀;x.y.e₁\}(n)] : X$$
\begin{code}
natrec : {X : Set} → ℕ → X → (ℕ → X → X) → X
natrec zero e₀ e₁ = e₀
natrec (suc n) e₀ e₁ = e₁ n (natrec n e₀ e₁)
\end{code}

Since we are in a dependently typed setting, however, we prove theorems as well
as write programs. Therefore, we can see this recursion principle as a special
case of the induction principle \term{natind}, which represents the by induction
for the natural numbers. One may notice that while the types are different, the
programs \term{natrec} and \term{natind} are actually the same, up to
α-equivalence. One can therefore, as a corollary, actually just include the type
infomation and Agda can infer the speciliazation for you, as seen in
\term{natrec'} below.

\[
  \begin{prooftree}
    \hypo{̌\Gamma, x : ℕ \vdash X : {\rm type} }
    \hypo{\Gamma \vdash n : ℕ }
    \hypo{\Gamma \vdash e₀ : X[x := 0] }
    \hypo{\Gamma, y : ℕ, z : X[x := y] \vdash e₁ : X[x := suc\ y]}
    \infer4[]{\Gamma \vdash natind\{e₀,\;x.y.e₁\}(n) : X[x := n]}
  \end{prooftree}
\]
$$\Gamma \vdash natind\{e₀;x.y.e₁\}(n) \equiv e₀ : X[x := 0]$$
$$\Gamma \vdash natind\{e₀;x.y.e₁\}(suc\ n) \equiv e₁[x := n,y := natind\{e₀;x.y.e₁\}(n)] : X[x := suc\ n]$$
\begin{code}
natind : {X : ℕ → Set} → (n : ℕ) → X zero → ((n : ℕ) → X n → X (suc n)) → X n
natind zero base step = base
natind (suc n) base step = step n (natind n base step)

natrec' : {X : Set} → ℕ → X → (ℕ → X → X) → X
natrec' = natind
\end{code}
We will defer the details of using induction and recursion principles for later
when we actually give examples of pidgin proofs some of our grammars can
handle.
