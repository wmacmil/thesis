\begin{code}[hide]
--{-# OPTIONS --cubical #-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module monoid where

module Namespace1 where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Structure
  open import Cubical.Algebra.Group.Base
  open import Cubical.Data.Sigma

  private
    variable
      ℓ ℓ' ℓ'' ℓ''' : Level

\end{code}

\begin{code}

  isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
  isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)

  record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
    constructor grouphom

    field
      fun : ⟨ G ⟩ → ⟨ H ⟩
      isHom : isGroupHom G H fun

\end{code}

This actually \emph{was} the Cubical Agda implementation of a group homomorphism
sometime around the end of 2020. We see that, while a mathematician might be
able to infer the meaning of some of the syntax, the use of levels, the
distinguising bewteen isGroupHom and GroupHom itself, and many other details
might obscure what's going on.

We provide the current, as of May 2021, definition via Cubical Agda. One may
witness a significant number of differences from the previous version :
concrete syntax differenes via changes in camel case, new uses of Group vs
GroupStr, as well as, most significantly, the identity and inverse preservation
data not appearing as corollaries, but part of the definition. Additionally, we
had to refactor the commented lines to those shown below to be compatible with
our outdated version of cubical.  These changes would not just be interesting
to look at from the author of the libraries's perspective, but also
syntactically.

\begin{code}

  record IsGroupHom {A : Type ℓ} {B : Type ℓ'}
    (M : GroupStr A) (f : A → B) (N : GroupStr B)
    : Type (ℓ-max ℓ ℓ')
    where

    -- Shorter qualified names
    private
      module M = GroupStr M
      module N = GroupStr N

    field
      pres· : (x y : A) → f (M._+_ x y) ≡ (N._+_ (f x) (f y))
      pres1 : f M.0g ≡ N.0g
      presinv : (x : A) → f (M.-_ x) ≡ N.-_ (f x)
      -- pres· : (x y : A) → f (x M.· y) ≡ f x N.· f y
      -- pres1 : f M.1g ≡ N.1g
      -- presinv : (x : A) → f (M.inv x) ≡ N.inv (f x)

  GroupHom' : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
  -- GroupHom' : (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
  GroupHom' G H = Σ[ f ∈ (G .fst → H .fst) ] IsGroupHom (G .snd) f (H .snd)

\end{code}
