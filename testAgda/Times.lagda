\begin{code}

module Times where

open import Nat
open import Plus

times : ℕ → ℕ → ℕ
times z y = z
times (s x) y = plus y (times x y)

\end{code}
