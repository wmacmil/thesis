\begin{code}[hide]

module primitives where

\end{code}

Formation rules, are given by the data declaration, followed by some number of
constructors which correspond to the 


A proof the proof-theoretic this looks like the following


\begin{prooftree}
  \hypo{ \Gamma, A &\vdash B }
  \infer1[abs]{ \Gamma &\vdash A\to B }
  \hypo{ \Gamma \vdash A }
  \infer2[app]{ \Gamma \vdash B }
\end{prooftree}


\begin{code}

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

\end{code}


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
