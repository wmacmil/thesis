
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

\begin{code}

isContr : (A : Set) → Set
isContr A =  Σ A λ a → (x : A) → (a ≡ x)

Equivalence : (A B : Set) → (f : A → B) → Set
Equivalence A B f = ∀ (y : B) → isContr (fiber' y)
  where
    fiber' : (y : B) → Set
    fiber' y = Σ A (λ x → y ≡ f x) 

\end{code}
