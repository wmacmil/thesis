
\begin{code}[hide]

-- {-# OPTIONS --omega-in-omega --type-in-type #-}

module ex where

\end{code}


Formation rules, are given by the first line of the data declaration, followed
by some number of constructors which correspond to the introduction forms of the
type being defined.

Therefore, to define a type  Booleans, 𝔹, we present for the formation rule

\[
  \begin{prooftree-- }
    \infer1[]{ \vdash 𝔹 : {\rm type}}
  \end{prooftree}
\]

along with two introduction rules for the bits,

\[
  \begin{prooftree}
    \infer1[]{ \Gamma \vdash true : 𝔹  }
  \end{prooftree}
  \quad \quad
  \begin{prooftree}
    \infer1[]{ \Gamma \vdash false : 𝔹  }
  \end{prooftree}
\]

Agda's allows us to succintly put these together as

\begin{code}

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

\end{code}

Now we can define our first type, term judgement pair, and define, for instance,
the Boolean or, ∨. We detail the definition which is just a result of the
pattern match Agda performs when working interactively via holes in the emacs
mode, and that once one plays around with it, one recognizes both the beauty and
elegance in how Agda can help one facilitate building a program. The colon
reresents the judgmenet that ∨ is a type, whereas the equality symbol denotes
the fact that ∨ is computationally equal to the subsequent expression over the
given inputs. Once one has made this equality judgement, agda can normalize the
definitionally equal terms to the same normal form when defining subsequent
judgements.

The underscore denotes the placement of the arguement. We see the _∨_
constructor allows for more nuanced syntacic features out of the box than most
programming languages provide, like unicode and various ways of mixing
arguements into the function. This is interesting from the emph{concrete syntax}
perspective as the arguement placement, and symbolic expressiveness gives Agda a
syntax more familiar to the mathematician.

\begin{code}

_∨_ : 𝔹 → 𝔹 → 𝔹
true  ∨ b     = true
false ∨ true  = true
false ∨ false = false

\end{code}


As the elimination forms are deriveable from the introduction rules, the
computation rules can then be extracted by via the harmonious relationship
between the introduction and elmination forms \cite{pfenningHar}. Agda's pattern
matching is equivalent to the deriveable dependently typed elimination forms
\cite{coqPat}, and one can simply pattern match on a boolean, producing multiple
lines for each constructor of the variable's type, to extract the classic
recursion principle for Booleans.

\[
  \begin{prooftree}
    \hypo{̌\Gamma \vdash A : {\rm type} }
    \hypo{\Gamma \vdash b : 𝔹 }
    \hypo{\Gamma \vdash a1 : A}
    \hypo{\Gamma \vdash a2 : A }
    \infer4[]{\Gamma \vdash boolrec\{a1;a2\}(b) : A }
  \end{prooftree}
\]


\begin{code}

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if true then a1 else a2 = a1
if false then a1 else a2 = a2

\end{code}

The Agda code reflects this, and we see the first use of parametric
polymorphism, namely, that we can extract a member of some arbtitrary type \term{A} from a boolean
value given two possibly equal values members of \term{A}.

This polymorphism therefore allows one to implement simple programs like the
boolean not, ~, via the eliminator. More interestingly, one can work with
functionals, or higher order functions which take functions as arguements and
return functions as well. We also notice in \term{functionalExample} below that
one can work directly with lambda's if the typechecker infers a function type
for a hole.

\begin{code}

~ : 𝔹 → 𝔹
~ b = if b then false else true

functionalExample : 𝔹 → (𝔹 → 𝔹) → (𝔹 → 𝔹)
functionalExample b f = if b then f else λ b' → f (~ b')

\end{code}

This simple example

\begin{code}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

ℕrec : {X : Set} -> (ℕ -> X -> X) -> X -> ℕ -> X
ℕrec f x zero = x
ℕrec f x (suc n) = f n (ℕrec f x n)

-- data List (A : Type) : Type where


-- data Vector :



-- \begin{code}

-- Type : Set₁
-- Type = Set

-- \end{code}
\end{code}
