\begin{code}[hide]

data aℕ : Set where
 zero : aℕ

variable
  A : Set
  D : Set
  stuff : Set

definition-body : aℕ → Set
definition-body  zero = aℕ

T = aℕ → aℕ
L = aℕ
E = aℕ
C = aℕ

proof : L
proof = zero

corollaryStuff = aℕ

proofNeedingLemma : aℕ → aℕ → aℕ
proofNeedingLemma x = λ x₁ → zero

\end{code}

\begin{code}

--commentary

data inductiveType : Set where --Formation Rule
  constructr  : inductiveType --Introduction Rules
  constructr' : inductiveType

postulate   -- Axiom
  axiom : A

definition : stuff → Set
definition s = definition-body s

theorem : T     -- Theorem Statement
theorem = proofNeedingLemma lemma -- Proof
  where
    lemma : L     -- Lemma Statement
    lemma = proof

corollary : corollaryStuff → C
corollary coro-term = theorem coro-term
-- corallary = theorem zero

example : E     -- Example Statement
example = proof

\end{code}
