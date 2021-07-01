\begin{code}

module Plus where

open import Nat

plus : ℕ → ℕ → ℕ
plus z x₁ = x₁
plus (s x) x₁ = s (plus x x₁)

\end{code}
