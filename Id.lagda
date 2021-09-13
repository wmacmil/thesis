\begin{code}
module Id where

open import Agda.Builtin.Sigma public
open import Data.Product

data _≡_ {A : Set} (a : A) : A → Set where
  r : a ≡ a

infix 20 _≡_

-- (2.0.1)
J : {A : Set}
    → (D : (x y : A) → (x ≡ y) →  Set)
    -- → (d : (a : A) → (D a a r ))
    → ((a : A) → (D a a r ))
    → (x y : A)
    → (p : x ≡ y)
    ------------------------------------
    → D x y p
J D d x .x r = d x

-- Lemma 2.1.1
_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = y ≡ x
    d : (a : A) → D a a r
    d a = r

infixr 50 _⁻¹

-- Lemma 2.1.2
_∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
_∙_ {A} {x} {y} p {z} q = J D d x y p z q
    where
    D : (x₁ y₁ : A) → x₁ ≡ y₁ → Set
    D x y p = (z : A) → (q : y ≡ z) → x ≡ z
    d : (z₁ : A) → D z₁ z₁ r
    d = λ v z q → q

infixl 40 _∙_

-- Lemma 2.1.4 (i)_1
iₗ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ r ∙ p
iₗ {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ r ∙ p
    d : (a : A) → D a a r
    d a = r

-- Lemma 2.1.4 (i)_2
iᵣ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ r
iᵣ {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ p ∙ r
    d : (a : A) → D a a r
    d a = r

-- Lemma 2.1.4 (ii)_1
leftInverse : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ r
leftInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ∙ p ≡ r
    d : (x : A) → D x x r
    d x = r

-- Lemma 2.1.4 (ii)_2
rightInverse : {A : Set} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ r
rightInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ∙ p ⁻¹ ≡ r
    d : (a : A) → D a a r
    d a = r

-- Lemma 2.1.4 (iii)
doubleInv : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
doubleInv {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ⁻¹ ≡ p
    d : (a : A) → D a a r
    d a = r

-- Lemma 2.1.4 (iv)
associativity :{A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r' : z ≡ w )
  → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
associativity {A} {x} {y} {z} {w} p q r' = J D₁ d₁ x y p z w q r'
  where
    D₁ : (x y : A) → x ≡ y → Set
    D₁ x y p = (z w : A) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
    D₂ : (x z : A) → x ≡ z → Set
    D₂ x z q = (w : A) (r' : z ≡ w ) → r ∙ (q ∙ r') ≡ r ∙ q ∙ r'
    D₃ : (x w : A) → x ≡ w → Set
    D₃ x w r' =  r ∙ (r ∙ r') ≡ r ∙ r ∙ r'
    d₃ : (x : A) → D₃ x x r
    d₃ x = r
    d₂ : (x : A) → D₂ x x r
    d₂ x w r' = J D₃ d₃ x w r'
    d₁ : (x : A) → D₁ x x r
    d₁ x z w q r' = J D₂ d₂ x z q w r'

module Eckmann-Hilton where
  -- Lemma 2.1.6
  -- whiskering
  _∙ᵣ_ : {A : Set} → {b c : A} {a : A} {p q : a ≡ b} (α : p ≡ q) (r' : b ≡ c)
    → p ∙ r' ≡ q ∙ r'
  _∙ᵣ_ {A} {b} {c} {a} {p} {q} α r' = J D d b c r' a α
    where
      D : (b c : A) → b ≡ c → Set
      D b c r' = (a : A) {p q : a ≡ b} (α : p ≡ q) → p ∙ r' ≡ q ∙ r'
      d : (a : A) → D a a r
      d a a' {p} {q} α = iᵣ p ⁻¹ ∙ α ∙ iᵣ q

  _∙ₗ_ : {A : Set} → {a b : A} (q : a ≡ b) {c : A} {r' s : b ≡ c} (β : r' ≡ s)
    → q ∙ r' ≡ q ∙ s
  _∙ₗ_ {A} {a} {b} q {c} {r'} {s} β = J D d a b q c β
    where
      D : (a b : A) → a ≡ b → Set
      D a b q = (c : A) {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
      d : (a : A) → D a a r
      d a a' {r'} {s} β = iₗ r' ⁻¹ ∙ β ∙ iₗ s

  _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s)
    → p ∙ r' ≡ q ∙ s
  _⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)

  _⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s)
    → p ∙ r' ≡ q ∙ s
  _⋆'_ {A} {p = p} {s = s} α β =  (p ∙ₗ β) ∙ (α ∙ᵣ s)

  -- Definition 2.1.8
  -- loop space
  Ω : {A : Set} (a : A) → Set
  Ω {A} a = a ≡ a

  Ω² : {A : Set} (a : A) → Set
  Ω² {A} a = _≡_ {a ≡ a} r r

  lem1 : {A : Set} → (a : A) → (α β : Ω² {A} a)
    → (α ⋆ β) ≡ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r)
  lem1 a α β = r

  lem1' : {A : Set} → (a : A) → (α β : Ω² {A} a)
    → (α ⋆' β) ≡  (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)
  lem1' a α β = r

  -- Lemma 2.2.1
  -- first proof
  apf : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
  apf {A} {B} {x} {y} f p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = {f : A → B} → f x ≡ f y
      d : (x : A) → D x x r
      d = λ x → r

  lem20 : {A : Set} → {a : A} → (α : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ α
  lem20 α = iᵣ (α) ⁻¹

  lem21 : {A : Set} → {a : A} → (β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ β
  lem21 β = iᵣ (β) ⁻¹

  lem2 : {A : Set} → (a : A) → (α β : Ω² {A} a)
    → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ (α ∙ β)
  lem2 {A} a α β =
    apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) )
        (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

  lem2' : {A : Set} → (a : A) → (α β : Ω² {A} a)
    → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ (β ∙ α )
  lem2' {A} a α β =
    apf (λ - → - ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r))
      (lem21 β) ∙ apf (λ - → β ∙ -) (lem20 α)

  ⋆≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (α ∙ β)
  ⋆≡∙ a α β = lem1 a α β ∙ lem2 a α β

  ⋆'≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡ (β ∙ α)
  ⋆'≡∙ a α β = lem1' a α β ∙ lem2' a α β

  _⋆≡⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s)
    → (α ⋆ β) ≡ (α ⋆' β)
  _⋆≡⋆'_ {A} {a} {b} {c} {p} {q} {r'} {s} α β = J D d p q α c r' s β
    where
      D : (p q : a ≡ b) → p ≡ q → Set
      D p q α = (c : A) (r' s : b ≡ c) (β : r' ≡ s) → (α ⋆ β) ≡ (α ⋆' β)
      E : (r' s : b ≡ c) → r' ≡ s → Set
      E r' s β =
        (_⋆_ {A} {b = b} {c} {r} {r} {r' = r'} {s = s} r β) ≡ (r ⋆' β)
      e : ((s : b ≡ c) → E s s r)
      e r = r
      d : ((p : a ≡ b) → D p p r)
      d r a r r r = r -- book uses J

  -- cheating, not using the same arguement as the book
  eckmannHilton : {A : Set} → (a : A) → (α β : Ω² {A} a) → α ∙ β ≡ β ∙ α
  eckmannHilton a r r = r

open Eckmann-Hilton

-- Lemma 2.2.2 (i)
apfHom : {A B : Set} {x y z : A} (p : x ≡ y) (f : A → B) (q : y ≡ z)
  → apf f (p ∙ q) ≡ (apf f p) ∙ (apf f q)
apfHom {A} {B} {x} {y} {z} p f q = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} {q : y ≡ z} → apf f (p ∙ q) ≡ (apf f p) ∙ (apf f q)
    d : (x : A) → D x x r
    d x = r

-- Lemma 2.2.2 (ii)
apfInv : {A B : Set} {x y : A} (p : x ≡ y) (f : A → B) → apf f (p ⁻¹) ≡ (apf f p) ⁻¹
apfInv {A} {B} {x} {y} p f = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} → apf f (p ⁻¹) ≡ (apf f p) ⁻¹
    d : (x : A) → D x x r
    d x = r

-- compostion, not defined in hott book
infixl 40 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- Lemma 2.2.2 (iii)
apfComp : {A B C : Set} {x y : A} (p : x ≡ y) (f : A → B) (g : B → C)
  → apf g (apf f p) ≡ apf (g ∘ f) p
apfComp {A} {B} {C} {x} {y} p f g = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} {g : B → C} → apf g (apf f p) ≡ apf (g ∘ f) p
    d : (x : A) → D x x r
    d x = r

id : {A : Set} → A → A
id = λ z → z

-- Lemma 2.2.2 (iv)
apfId : {A : Set} {x y : A} (p : x ≡ y) → apf id p ≡ p
apfId {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = apf id p ≡ p
    d : (x : A) → D x x r
    d = λ x → r

-- Lemma 2.3.1
transport : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y
transport {A} {P} {x} {y} = J D d x y
  where
    D : (x y : A) → x ≡ y → Set
    D x y p =  P x → P y
    d : (x : A) → D x x r
    d = λ x → id

p* : {A : Set} {P : A → Set} {x : A} {y : A} {p : x ≡ y} → P x → P y
p* {P = P} {p = p} u = transport p u

_* : {A : Set} {P : A → Set} {x : A} {y : A} (p : x ≡ y) → P x → P y
(p *) u = transport p u


-- Lemma 2.3.2
lift : {A : Set} {P : A → Set} {x y : A}  (u : P x) (p : x ≡ y)
  → (x , u) ≡ (y , p* {P = P} {p = p} u)
lift {P} u r = r

-- Lemma 2.3.4
apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} {p : x ≡ y}
  → p* {P = P} {p = p} (f x) ≡ f y
apd {A} {P} f {x} {y} {p} = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p* {P = P} {p = p} (f x) ≡ f y
    d : (x : A) → D x x r
    d = λ x → r

-- Lemma 2.3.5
transportconst : {A B : Set} {x y : A} {p : x ≡ y} (b : B)
  → transport {P = λ _ → B} p b ≡ b
transportconst {A} {B} {x} {y} {p} b = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = transport {P = λ _ → B} p b ≡ b
    d : (x : A) → D x x r
    d = λ x → r

-- missing 2.3.8

-- Lemma 2.3.9
twothreenine : {A : Set} {P : A → Set} {x y z : A}  (p : x ≡ y) (q : y ≡ z ) {u : P x}
  → ((q *) (_* {P = P} p u)) ≡ (((p ∙ q) *) u)
twothreenine r r = r

-- Lemma 2.3.10
twothreeten : {A B : Set} {f : A → B} {P : B → Set} {x y : A} (p : x ≡ y)
  {u : P (f x) } → transport p u ≡ transport {P = P} (apf f p) u
twothreeten r = r

-- Lemma 2.3.11
twothreeeleven : {A : Set} {P Q : A → Set} {f : (x : A) → P x → Q x} {x y : A}
  (p : x ≡ y) {u : P x} → transport {P = Q} p (f x u) ≡ f y (transport p u)
twothreeeleven r = r

infixl 20 _~_
-- Lemma 2.4.1
_~_ : {A : Set} {P : A → Set} (f g : (x : A) → P x) → Set
f ~ g  = (x : _) → f x ≡ g x

-- Lemma 2.4.2 (i)
refl~ : {A : Set} {P : A → Set} → ((f : (x : A) → P x) → f ~ f)
refl~ f x = r

-- Lemma 2.4.2 (ii)
sym~ : {A : Set} {P : A → Set} → (f g : (x : A) → P x) → f ~ g → g ~ f
sym~ f g fg = λ x → fg x ⁻¹

-- Lemma 2.4.2 (iii)
trans~ : {A : Set} {P : A → Set} → (f g h : (x : A) → P x) → f ~ g → g ~ h → f ~ h
trans~ f g h fg gh = λ x → (fg x) ∙ (gh x)

-- transrightidentity, note not defitionally equal
translemma : {A : Set} {x y : A} (p : x ≡ y) → p ∙ r ≡ p
translemma r = r

-- Lemma 2.4.3
hmtpyNatural : {A B : Set} {f g : A → B} {x y : A} (p : x ≡ y)
  → ((H : f ~ g) → H x ∙ apf g p ≡ apf f p ∙ H y )
hmtpyNatural {x = x} r H = translemma (H x)

-- syntactic sugar for equational reasoning
-- from Wadler's presentation
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  x≡y ∙ y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  = r

open ≡-Reasoning

-- Corollary 2.4.4
coroll :  {A B : Set} {f : A → A} {x y : A} (p : x ≡ y)
  → ((H : f ~ (id {A})) → H (f x) ≡ apf f (H x) )
coroll {A} {f = f} {x = x} p H =
  begin
    H (f x)
  ≡⟨ translemma (H (f x)) ⁻¹ ⟩
    H (f x) ∙ r
  ≡⟨ apf (λ - → H (f x) ∙ -) ll51 ⟩
    H (f x) ∙ (apf (λ z → z) (H x) ∙ H x ⁻¹ )
  ≡⟨ associativity (H (f x)) (apf (λ z → z) (H x)) ((H x ⁻¹)) ⟩
    H (f x) ∙ apf (λ z → z) (H x) ∙ H x ⁻¹
  ≡⟨ whisk ⟩
    apf f (H x) ∙ H (x) ∙ H x ⁻¹
  ≡⟨ associativity (apf f (H x)) (H (x)) (H x ⁻¹) ⁻¹ ⟩
    apf f (H x) ∙ (H (x) ∙ H x ⁻¹)
  ≡⟨ apf (λ - → apf f (H x) ∙ -) locallem ⟩
    apf f (H x) ∙ r
  ≡⟨ translemma (apf f (H x)) ⟩
    apf f (H x) ∎
  where
    thatis : H (f x) ∙ apf (λ z → z) (H x) ≡ apf f (H x) ∙ H (x)
    thatis = hmtpyNatural (H x) H
    whisk : H (f x) ∙ apf (λ z → z) (H x) ∙ H x ⁻¹ ≡ apf f (H x) ∙ H (x) ∙ H x ⁻¹
    whisk = thatis ∙ᵣ (H x ⁻¹)
    locallem :  H x ∙ H x ⁻¹ ≡ r
    locallem = rightInverse (H x)
    ll51 : r ≡ apf (λ z → z) (H x) ∙ H x ⁻¹
    ll51 = locallem ⁻¹ ∙ (apf (λ - → - ∙ H x ⁻¹) (apfId (H x))) ⁻¹

-- Definition 2.4.6
qinv : {A B : Set} → (f : A → B) → Set
qinv {A} {B} f = Σ (B → A) λ g → (f ∘ g ~ id {B}) ×  (g ∘ f ~ id {A})

-- Example 2.4.7
qinvid : {A : Set} → qinv {A} {A} id
qinvid = id , (λ x → r) , λ x → r

-- syntactic sugar, is redundant
p∙ : {A : Set} {x y z : A} (p : x ≡ y) → ((y ≡ z) → (x ≡ z))
p∙ p = λ - → p ∙ -

-- Example 2.4.8
qinvcomp : {A : Set} {x y z : A} (p : x ≡ y) → qinv (p∙ {A} {x} {y} {z} p)
qinvcomp p = (λ - → p ⁻¹ ∙ -) , sec , retr
  where
    sec : (λ x → p∙ p (p ⁻¹ ∙ x)) ~ (λ z → z)
    sec x =
      begin
        p∙ p (p ⁻¹ ∙ x)
      ≡⟨ associativity p (p ⁻¹) x ⟩
        (p ∙ p ⁻¹) ∙ x
      ≡⟨ apf (λ - → - ∙ x) (rightInverse p) ⟩
        r ∙ x
      ≡⟨ iₗ x ⁻¹ ⟩
        x ∎
    retr : (λ x → p ⁻¹ ∙ p∙ p x) ~ (λ z → z)
    retr x =
      begin
        p ⁻¹ ∙ p∙ p x
      ≡⟨ associativity (p ⁻¹) p x ⟩
        (p ⁻¹ ∙ p) ∙ x
      ≡⟨ apf (λ - → - ∙ x) (leftInverse p) ⟩
        x ∎


-- Example 2.4.9
qinvtransp : {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)
  → qinv (transport {P = P} p)
qinvtransp {A} {P} {x} {y} p = transport (p ⁻¹) , sec , retr p
  where
    sec' : {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)
      → (λ x₁ → transport {P = P} p (transport (p ⁻¹) x₁)) ~ (λ z → z)
    sec' r x = r
    sec : (λ x₁ → transport p (transport (p ⁻¹) x₁)) ~ (λ z → z)
    sec z = sec' p z
    retr : (p : x ≡ y) → (λ x₁ → transport (p ⁻¹) (transport p x₁)) ~ (λ z → z)
    retr r z = r

-- Definition 2.4.10
isequiv : {A B : Set} → (f : A → B) → Set
isequiv {A} {B} f = Σ (B → A) λ g → (f ∘ g ~ id {B}) ×
                    Σ (B → A) λ g → (g ∘ f ~ id {A})

-- (i) prior to 2.4.10
qinv->isequiv : {A B : Set} → (f : A → B) → qinv f → isequiv f
qinv->isequiv f (g , α , β) = g , α , g , β

-- (ii) prior to 2.4.10
-- not the same is as the book
isequiv->qinv : {A B : Set} → (f : A → B) →  isequiv f → qinv f
isequiv->qinv f (g , α , g' , β ) = (g' ∘ f ∘ g) , sec , retr
  where
    sec : (λ x → f (g' (f (g x)))) ~ (λ z → z)
    sec x = apf f (β (g x)) ∙ α x
    retr : (λ x → g' (f (g (f x)))) ~ (λ z → z)
    retr x = apf g' (α (f x)) ∙ β x

isequiv->qinv' : {A B : Set} → (f : A → B) →  isequiv f → qinv f
isequiv->qinv' f (g , α , h , β ) = g , α , β'
  where
    γ : (λ x → g x) ~ λ x → h x
    γ x = β (g x) ⁻¹ ∙ apf h (α x)
    β' : (λ x → g (f x)) ~ (λ z → z)
    β' x = (γ (f x)) ∙ β x

-- Definition 2.4.11
_≃_ : (A B : Set) → Set
A ≃ B = Σ (A → B) λ f → isequiv f

-- Lemma 2.4.12 (i)
≃refl : {A : Set} → A ≃ A
≃refl = (id) , (qi qinvid)
  where
    qi : qinv (λ z → z) → isequiv (λ z → z)
    qi = qinv->isequiv (id )
-- type equivalence is an equivalence relation, 2.4.12
-- qinv->isequiv

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = (b , a)

-- Lemma 2.4.12 (ii)
≃sym : {A B : Set} → A ≃ B → B ≃ A
≃sym (f , eqf) = f-1 , ef (f , comm× sndqf)
  where
    qf : isequiv f → qinv f
    qf = isequiv->qinv f
    f-1 : _ → _
    f-1 = fst (qf eqf)
    sndqf : ((λ x → f (fst (isequiv->qinv f eqf) x)) ~ (λ z → z)) ×
              ((λ x → fst (isequiv->qinv f eqf) (f x)) ~ (λ z → z))
    sndqf = snd (qf eqf)
    ef : qinv f-1 → isequiv f-1
    ef = qinv->isequiv f-1

-- Lemma 2.4.12 (iii)
≃trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃trans (f , eqf) (g , eqg) = (g ∘ f) ,
  qinv->isequiv (λ z → g (f z)) ((f-1 ∘ g-1) , sec , retr)
  where
    qf : isequiv f → qinv f
    qf = isequiv->qinv f
    f-1 = fst (qf eqf)
    qg : isequiv g → qinv g
    qg = isequiv->qinv g
    g-1 = fst (qg eqg)
    sec : (λ x → g (f (f-1 (g-1 x)))) ~ (λ z → z)
    sec x =
            begin g (f (f-1 (g-1 x)))
            ≡⟨ apf g (fst (snd (qf eqf)) (g-1 x)) ⟩
            g (g-1 x)
            ≡⟨ fst (snd (qg eqg)) x ⟩
            x ∎
    retr : (λ x → f-1 (g-1 (g (f x)))) ~ (λ z → z)
    retr x =
             begin f-1 (g-1 (g (f x)))
             ≡⟨ apf f-1 ((snd (snd (qg eqg)) (f x))) ⟩
             f-1 (f x)
             ≡⟨ snd (snd (qf eqf)) x ⟩
             x ∎

-- No section 2.5

-- Lemma 2.6.1
fprodId : {A B : Set} {x y : A × B} → _≡_ {A × B} x y
  → ((fst x) ≡ (fst y)) × ((snd x) ≡ (snd y))
fprodId p = (apf fst p) , (apf snd p)
-- fprodId r = r , r

-- Theorem 2.6.2
equivfprod : {A B : Set} (x y : A × B) → isequiv (fprodId {x = x} {y = y} )
equivfprod (x1 , y1) (x2 , y2) = qinv->isequiv fprodId (sn , h1 , h2)
  where
    sn : (x1 ≡ x2) × (y1 ≡ y2) → (x1 , y1) ≡ (x2 , y2)
    sn (r , r) = r
    h1 : (λ x → fprodId (sn x)) ~ (λ z → z)
    h1 (r , r) = r
    -- h1 (r , r) = r
    h2 : (λ x → sn (fprodId x)) ~ (λ z → z)
    h2 r = r

-- helper type for below
×fam : {Z : Set} {A B : Z → Set} → (Z → Set)
×fam {A = A} {B = B} z = A z × B z

-- Theorem 2.6.4
transport× : {Z : Set} {A B : Z → Set} {z w : Z} (p : z ≡ w)
             (x : ×fam {Z} {A} {B} z)
  → (transport p x ) ≡ (transport {Z} {A} p (fst x) , transport {Z} {B} p (snd x))
transport× r s = r

fprod : {A B A' B' : Set} (g : A → A') (h : B → B') → (A × B → A' × B')
fprod g h x = g (fst x) , h (snd x)

-- inverse of fprodId
pair= : {A B : Set} {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
pair= (r , r) = r

-- Theorem 2.6.5
functorProdEq : {A B A' B' : Set} (g : A → A') (h : B → B')
                (x y : A × B) (p : fst x ≡ fst y) (q : snd x ≡ snd y)
  → apf (λ - → fprod g h -) (pair= (p , q)) ≡ pair= (apf g p , apf h q)
functorProdEq g h (a , b) (.a , .b) r r = r

-- Theorem 2.7.2
equivfDprod : {A : Set} {P : A → Set} (w w' : Σ A (λ x → P x))
  → (w ≡ w') ≃ Σ (fst w ≡ fst w') λ p → p* {p = p} (snd w) ≡ snd w'
equivfDprod (w1 , w2) (w1' , w2') = f , qinv->isequiv f (f-1 , ff-1 , f-1f)
  where
    f : (w1 , w2) ≡ (w1' , w2') → Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2')
    f r = r , r
    f-1 : Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2') → (w1 , w2) ≡ (w1' , w2')
    f-1 (r , r) = r
    ff-1 : (λ x → f (f-1 x)) ~ (λ z → z)
    ff-1 (r , r) = r
    f-1f : (λ x → f-1 (f x)) ~ (λ z → z)
    f-1f r = r

-- Corollary 2.7.3
etaDprod : {A : Set} {P : A → Set} (z : Σ A (λ x → P x)) → z ≡ (fst z , snd z)
etaDprod z = r

-- helper type for 2.7.4
Σfam : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) → (A → Set)
Σfam {P = P} Q x = Σ (P x) λ u → Q (x , u)

-- helper function for 2.7.4
dpair= : {A : Set} {P : A → Set} {w1 w1' : A} {w2 : P w1 } {w2' : P w1'}
  → (p : Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2')) → (w1 , w2) ≡ (w1' , w2')
dpair= (r  , r) = r

-- Theorem 2.7.4
transportΣ : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) (x y : A) (p : x ≡ y)
  ((u , z) : Σfam Q x)
  → _* {P = λ - → Σfam Q - } p (u , z) ≡
    ((p *) u  , _* {P = λ - → Q ((fst -) , (snd -))} (dpair= (p , r)) z)
transportΣ Q x .x r (u , z) = r

fDprod : {A A' : Set} {P : A → Set} {Q : A' → Set} (g : A → A')
  (h : (a : A) →  P a → Q (g a))
  → (Σ A λ a → P a) → (Σ A' λ a' → Q a')
fDprod g h (a , pa) = g a , h a pa

ap2 : {A B C : Set} {x x' : A} {y y' : B} (f : A → B → C)
      → (x ≡ x') → (y ≡ y') → (f x y ≡ f x' y')
ap2 f r r = r

transportd : {X : Set } (A : X → Set  ) (B : (x : X) → A x → Set )
  {x : X} ((a , b) : Σ (A x) λ a → B x a) {y : X} (p : x ≡ y)
  → B x a → B y (transport {P = A} p a)
transportd A B (a , b) r = id

data Unit : Set where
  ⋆ : Unit

-- Theorem 2.8.1
path1 : (x y : Unit) → (x ≡ y) ≃ Unit
path1 x y = (λ p → ⋆) , qinv->isequiv (λ p → ⋆) (f-1 x y , ff-1 , f-1f x y)
  where
    f-1 : (x y : Unit) → Unit → x ≡ y
    f-1 ⋆ ⋆ ⋆ = r
    ff-1 : (λ x₁ → ⋆) ~ (λ z → z)
    ff-1 ⋆ = r
    f-1f : (x y : Unit) → (λ _ → f-1 x y ⋆) ~ (λ z → z)
    f-1f ⋆ .⋆ r = r

-- 2.9

-- theorem 2.9.2
happly : {A : Set} {B : A → Set} {f g : (x : A) → B x} → f ≡ g
  → ((x : A) → f x ≡ g x )
happly r x = r

postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} →
    ((x : A) → f x ≡ g x ) → f ≡ g

->fam : {X : Set} (A B : X → Set) → X → Set
->fam A B x = A x → B x

-- Lemma 2.9.4
transportF : {X : Set} {A B : X → Set} {x1 x2 : X} {p : x1 ≡ x2} {f : A x1 → B x1}
  → transport {P = ->fam A B} p f ≡  λ x
  → transport {P = B} p (f (transport {P = A} (p ⁻¹) x))
transportF {X} {A} {B} {x1} {.x1} {r} {f} = funext (λ x → r)
\end{code}
