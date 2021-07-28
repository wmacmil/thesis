\begin{code}[hide]

module introAgda where

\end{code}

Formation rules, are given by the data declaration, followed by some number of
constructors which correspond to the 


\begin{code}

-- data 𝔹 : Set where
--   true : 𝔹
--   false : 𝔹

\end{code}

A proof the proof-theoretic this looks like the following

\[
  \begin{prooftree}
    \infer0{ \vdash A }
    \hypo{ \vdash B } \infer1{ \vdash B, C }
    \infer2{ \vdash A\wedge B, C }
  \end{prooftree}
\]


-- $ \frac{\Gamma, x : A \vdash b : B} {\Gamma \vdash \lambda x. b : A \rightarrow
-- B} $

\begin{code}

-- if_then_else_ : {A : Set} → 𝔹 → A → A → A
-- if true then a1 else a2 = a1
-- if false then a1 else a2 = a2

\end{code}

-- data ℕ : Type where
--   zero : ℕ
--   suc  : ℕ → ℕ

-- data List (A : Type) : Type where
  

-- data Vector : 



-- \begin{code}

-- Type : Set₁
-- Type = Set

-- \end{code}
