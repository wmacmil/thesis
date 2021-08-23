\begin{code}[hide]

-- {-# OPTIONS --omega-in-omega --type-in-type #-}

module nproof where

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_+_) public
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

\end{code}

\begin{code}[hide]
ℕrec : {X : Set} -> (ℕ -> X -> X) -> X -> ℕ -> X
ℕrec f x zero = x
ℕrec f x (suc n) = f n (ℕrec f x n)

natrec : {X : Set} → ℕ → X → (ℕ → X → X) → X
natrec zero e₀ e₁ = e₀
natrec (suc n) e₀ e₁ = e₁ n (natrec n e₀ e₁)

natind : {X : ℕ → Set} → (n : ℕ) → X zero → ((n : ℕ) → X n → X (suc n)) → X n
natind zero base step = base
natind (suc n) base step = step n (natind n base step)


\end{code}


\begin{code}
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc x + n = suc (x + n)

2+2=4 : 2 + 2 ≡ 4
2+2=4 = refl

0+n=n : ∀ (n : ℕ) → 0 + n ≡ n
0+n=n n = refl
\end{code}

\begin{code}[hide]
postulate
  roadblockn : ∀ (m : ℕ) → m + zero ≡ m -- identity cancels on the left

roadblock = λ (n : ℕ) → roadblockn n
\end{code}

\begin{code}[hide]
n+0=n : ∀ (n : ℕ) → n + 0 ≡ n
n+0=n = roadblock
\end{code}
