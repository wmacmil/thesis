
\begin{code}[hide]
{-# OPTIONS --omega-in-omega --type-in-type #-}

module ContrClean where

open import Agda.Builtin.Sigma public

variable
  A B : Set

data _≡_ {A : Set} (a : A) : A → Set where
  r : a ≡ a

infix 20 _≡_

id : A → A
id = λ z → z

\end{code}

\begin{figure}[H]
\textbf{Definition}:
A type $A$ is contractible, if there is $a : A$, called the center of contraction, such that for all $x : A$, $\equalH {a}{x}$.
\begin{verbatim}
isContr ( A : Set ) : Set = ( a : A ) ( * ) ( ( x : A ) -> Id ( a ) ( x ) )
\end{verbatim}
\begin{code}
isContr : (A : Set) → Set
isContr A =  Σ A λ a → (x : A) → (a ≡ x)
\end{code}
\caption{Contractibility} \label{fig:R1}
\end{figure}

In \autoref{fig:R3}, we show the different syntax presentations of the notion of
\emph{equivalence}, which is merely a bijection when restricted to sets. This is
of such fundamental importance in mathematics that it merits its own chapter in
the HoTT book, but we only showcase one of its many equivalent definitions. We
see that the pidgin syntax is stuck with the anaphoric artifact,
\codeword{fiber} has the type \codeword{it : Set} instead of something like
\codeword{(y : B) : Set}, and the \codeword{y} variable is unbound in the \codeword{fiber}
expression. This may possibly be fixed with a few hours more of tinkering, but
creates even more angst if we anticipate trying to translate proofs to Agda.

\begin{figure}[H]
\textbf{Definition}:
A map $f : \arrowH {A}{B}$ is an equivalence, if for all $y : B$, its fiber, $\comprehensionH {x}{A}{\equalH {\appH {f}{x}}{y}}$, is contractible.
We write $\equivalenceH {A}{B}$, if there is an equivalence $\arrowH {A}{B}$.
\begin{verbatim}
Equivalence ( f : A -> B ) : Set =
  ( y : B ) -> ( isContr ( fiber it ) ) ; ; ;
  fiber it : Set = ( x : A ) ( * ) ( Id ( f ( x ) ) ( y ) )
\end{verbatim}
\begin{code}
Equivalence : (A B : Set) → (f : A → B) → Set
Equivalence A B f = ∀ (y : B) → isContr (fiber' y)
  where
    fiber' : (y : B) → Set
    fiber' y = Σ A (λ x → y ≡ f x)
\end{code}
\caption{Contractibility} \label{fig:R3}
\end{figure}
