
\begin{code}[hide]

-- {-# OPTIONS --omega-in-omega --type-in-type #-}

module ex where

\end{code}


Formation rules, are given by the first line of the data declaration, followed
by some number of constructors which correspond to the introduction forms of the
type being defined.

Therefore, to define a type Booleans, we present for the formation rule

\[
  \begin{prooftree}
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

As the elimination forms are deriveable from the introduction rules, the
computation rules can then be extracted by via the harmonious relationship
between the introduction and elmination forms \cite{pfenningHar}. As Agda's pattern
matching is equivalent to the deriveable dependently typed elimination forms \cite{coqPat}, one can simply pattern match on a boolean variable to extract the classic recursion principle.

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
