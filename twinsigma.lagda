\subsection{Twin Primes Conjecture Revisited} \label{twin}
\begin{code}[hide]
module twinsigma where

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

isPrime : ℕ → Set
isPrime n =
  (n ≥ 2) ×
  ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))
\end{code}
We now give the dependent uncurring from the functions from \ref{twinprime} We
note that this perhaps is a bit more linguistically natural, because we can
refer to definitions of a prime number, sucessive prime numbers, etc. We leave
it to the reader to decide which presentation would be better suited for
translation.
\begin{code}
prime = Σ[ p ∈ ℕ ] isPrime p

isSuccessivePrime : prime → prime → Set
isSuccessivePrime (p , pIsPrime) (p' , p'IsPrime) =
  ((p'' , p''IsPrime) : prime) →
  p ≤ p' → p ≤ p'' → p' ≤ p''

successivePrimes =
  Σ[ p ∈ prime ] Σ[ p' ∈ prime ] isSuccessivePrime p p'

primeGap : successivePrimes → ℕ
primeGap ((p , pIsPrime) , (p' , p'IsPrime) , p'-is-after-px) = p - p'

nth-pletPrimes : successivePrimes → ℕ → Set
nth-pletPrimes (p , p' , p'-is-after-p) n =
  primeGap (p , p' , p'-is-after-p) ≡ n

twinPrimes : successivePrimes →  Set
twinPrimes sucPrimes = nth-pletPrimes sucPrimes 2

twinPrimeConjecture : Set
twinPrimeConjecture = (n : ℕ) →
  Σ[ sprs@((p , p'), p'-after-p) ∈ successivePrimes ]
    (p ≥ n)
  × twinPrimes sprs
\end{code}
