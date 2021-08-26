\begin{code}[hide]
module twin-primes where

open import Data.Nat renaming (_+_ to _∔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum renaming (_⊎_ to _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m
\end{code}
\subsubsection{Formalizing The Twin Prime Conjecture}

Inspired by Escardos's formalization of the twin primes conjecture \cite{escardó2020introduction}, we intend to
demonstrate that while formalizing mathematics can be rewarding, it can also
create immense difficulties, especially if one wishes to do it in a way that
prioritizes natural language. The conjecture is incredibly compact

\begin{lem}
There are infinitely many twin primes.
\end{lem}

Somebody reading for the first time might then pose the immediate question : what is a twin prime?

\begin{definition}\label{def:def1}
A \emph{twin prime} is a prime number that is either 2 less or 2 more than another prime number
\end{definition}

Below Escardo's code is reproduced.
\begin{code}
isPrime : ℕ → Set
isPrime n =
  (n ≥ 2) ×
  ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

twinPrimeConjecture : Set
twinPrimeConjecture = (n : ℕ) → Σ[ p ∈ ℕ ] (p ≥ n)
  × isPrime p
  × isPrime (p ∔ 2)
\end{code}

We note there are some both subtle and big differences, between the natural
language claim. First, twin prime is defined implicitly via a product
expression, \term{×}. Additionally, the ``either 2 less or 2 more" clause is
oringially read as being interpreted as having ``2 more". This reading ignores
the symmetry of products, however, and both ``p or (p ∔ 2)" could be interpreted
as the twin prime. This phenomenon makes translation highly nontrivial; however,
we will later see that PGF is capable of adding a semantic layer where the
theorem can be evaluated during the translation. Finally, this theorem doesn't
say what it is to be infinite in general, because such a definition would
require a proving a bijection with the real numbers. In this case however, we
can rely on the order of the natural numbers, to simply state what it means to
have infinitely many primes.

Despite the beauty of this, mathematicians always look for alternative, more
general ways of stating things. Generalizing the notion of a twin prime is a
prime gap. And then one immediately has to ask what is a prime gap?

\begin{definition}\label{def:def2}
A \emph{twin prime} is a prime that has a prime gap of two.
\end{definition}
\begin{definition}\label{def:def3}
A \emph{prime gap} is the difference between two successive prime numbers.
\end{definition}

Now we're stuck, at least if you want to scour the internet for the definition
of ``two successive prime numbers". That is because any mathematician will take
for granted what it means, and it would be considered a waste of time and space
to include something \emph{everyone} alternatively knows. Agda, however, must
know in order to typecheck. Below we offer a presentation which suits Agda's
needs, and matches the number theorists presentation of twin prime.

\begin{code}
isSuccessivePrime : (p p' : ℕ) → isPrime p → isPrime p' → Set
isSuccessivePrime p p' x x₁ =
  (p'' : ℕ) → (isPrime p'') →
  p ≤ p' → p ≤ p'' → p' ≤ p''

primeGap :
  (p p' : ℕ) (pIsPrime : isPrime p) (p'IsPrime : isPrime p') →
  (isSuccessivePrime p p' pIsPrime p'IsPrime) →
  ℕ
primeGap p p' pIsPrime p'IsPrime p'-is-after-p = p - p'

twinPrime : (p : ℕ) → Set
twinPrime p =
  (pIsPrime : isPrime p) (p' : ℕ) (p'IsPrime : isPrime p')
  (p'-is-after-p : isSuccessivePrime p p' pIsPrime p'IsPrime) →
  (primeGap p p' pIsPrime p'IsPrime p'-is-after-p) ≡ 2

twinPrimeConjecture' : Set
twinPrimeConjecture' = (n : ℕ) → Σ[ p ∈ ℕ ] (p ≥ n)
  × twinPrime p
\end{code}


We see that \term{isSuccessivePrime} captures this meaning, interpreting
``successive" as the type of suprema in the prime number ordering. We also see that all the primality proofs must be given explicitly.

The term \term{primeGap} then has to reference this successive prime data, even
though most of it is discarded and unused in the actual program returning a
number. One could keep these unused arguements around via extra record fields,
to anticipate future programs calling \term{primeGap}, but ultimately the developer has to
decide what is relevant. A GF translation would ideally be kept as simple as possible. We also use propositional equality here, which is
another departure from classical mathematics, as will be elaborated later.

Finally, \{twinPrime} is a specialized version of \term{primeGap} to 2. ``has a
prime gap of two`` needs to be interpreted ``whose prime gap is equal to two",
and writing a GF grammar capable of disambiguating \emph{has} in mathematics
generally is likely impossible. One can also uncurry much of the above code to
make it more readable, which we include in the appendix \ref{twin}.

While working on this example, I tried to prove that 2 is prime in Agda with
this defintion. It turned out to be nontrivial. When I told this to an analyst
(in the mathematical sense) he remarked that couldn't possibly be the case
because it's something which a simple algorithm can compute (or generate). This
exchange was incredibly stimulating, for the mathematian didn't know about the
\emph{propositions as types} principle, and was simply taking for granted his
internal computational capacity to confuse it for proof, especially in a
constructive setting. He also seemed perplexed that anyone would find it
interesting to prove that 2 is prime. The proof that 2 is prime, via Agda's
standard libary, is done via reflection - a way of quoting a term into in
abstract syntax tree and then performing some kind of metacomputation. While
elegant, this obviously requires a lot of machinery, none of which would be easy
to communicate to a mathematician who doesn't know much about coding. As is
hopefully revealed by this discussion, seemingly trivial things, when treated by
the type theorist or linguist, can become wonderful areas of exploration.
