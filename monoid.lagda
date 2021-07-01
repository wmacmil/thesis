\begin{code}[hide]
{-# OPTIONS --cubical #-}

module monoid where

module Namespace1 where

  open import Cubical.Core.Everything
  open import Cubical.Foundations.Prelude renaming (_∙_ to _∙''_)
  open import Cubical.Foundations.Isomorphism

  private
    variable
      ℓ : Level

  is-left-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
  is-left-unit-for {A = A} e _⋆_ = (x : A) → e ⋆ x ≡ x

  is-right-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
  is-right-unit-for {A = A} e _⋆_ = (x : A) → x ⋆ e ≡ x

  is-assoc : {A : Type ℓ} → (A → A → A) → Type ℓ
  is-assoc {A = A} _⋆_ = (x y z : A) → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)

  record MonoidStrRec (A : Type ℓ) : Type ℓ where
    constructor
      monoid
    field
      ε   : A
      _∙_ : A → A → A

      left-unit  : is-left-unit-for ε _∙_
      right-unit : is-right-unit-for ε _∙_
      assoc      : is-assoc _∙_

      carrier-set : isSet A

  record Monoid' : Type (ℓ-suc ℓ) where
    constructor
      monoid'
    field
      A : Type ℓ
      ε   : A
      _∙_ : A → A → A

      left-unit  : is-left-unit-for ε _∙_
      right-unit : is-right-unit-for ε _∙_
      assoc      : is-assoc _∙_

      carrier-set : isSet A

\end{code}

\begin{code}
  monoidHom : {ℓ : Level}
            → ((monoid' a _ _ _ _ _ _) (monoid' a' _ _ _ _ _ _) : Monoid' {ℓ} )
            → (a → a') → Type ℓ
  monoidHom
    (monoid' A ε _∙_ left-unit right-unit assoc carrier-set)
    (monoid' A₁ ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁)
    f
    = (m1 m2 : A) → f (m1 ∙ m2) ≡ (f m1) ∙₁ (f m2)
\end{code}


