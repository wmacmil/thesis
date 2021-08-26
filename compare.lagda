\subsection{Hott and cubicalTT Grammars} \label{comparison}

\begin{code}[hide]
{-# OPTIONS --omega-in-omega --type-in-type #-}

module compare where

open import Agda.Builtin.Sigma public

variable
  A B : Set

data _≡_ {A : Set} (a : A) : A → Set where
  r : a ≡ a

infix 20 _≡_
\end{code}
\begin{code}
id : A → A
id = λ z → z

iscontr : (A : Set) → Set
iscontr A =  Σ A λ a → (x : A) → (a ≡ x)

fiber : (A B : Set) (f : A -> B) (y : B) → Set
fiber A B f y = Σ A (λ x → y ≡ f x)

isEquiv : (A B : Set) → (f : A → B) → Set
isEquiv A B f = (y : B) → iscontr (fiber A B f y)

isEquiv' : (A B : Set) → (f : A → B) → Set
isEquiv' A B f = ∀ (y : B) → iscontr (fiber' y)
  where
    fiber' : (y : B) → Set
    fiber' y = Σ A (λ x → y ≡ f x)

-- proof from Aarne
idIsEquiv' : (A : Set) → isEquiv A A (id {A})
idIsEquiv' A y = ybar , help
  where
    fib' : Set -- {y : A}
    fib' = fiber A A id y
    ybar : fib'
    ybar = y , r
    help : (x : fib') → _≡_ {Σ A (_≡_ y)} ybar x
    help = λ {(a , r) → r}

equiv : ( a b : Set ) → Set
equiv a b = Σ (a → b) λ f → isEquiv a b f

equivId : (x : Set) → equiv x x
equivId x = id , (idIsEquiv' x)

eqToIso : ( a b : Set ) → _≡_ {Set} a b → equiv a b
eqToIso a .a r = equivId a
\end{code}

Compared with the latex code

\begin{figure}[H]
 \textbf{Definition}:
 A type $A$ is contractible, if there is $a : A$, called the center of contraction, such that for all $x : A$, $\equalH {a}{x}$.

 \textbf{Definition}:
 A map $f : \arrowH {A}{B}$ is an equivalence, if for all $y : B$, its fiber, $\comprehensionH {x}{A}{\equalH {\appH {f}{x}}{y}}$, is contractible.
 We write $\equivalenceH {A}{B}$, if there is an equivalence $\arrowH {A}{B}$.

 \textbf{Lemma}:
 For each type $A$, the identity map, $\defineH {\idMapH {A}}{\typingH {\lambdaH {x}{A}{x}}{\arrowH {A}{A}}}$, is an equivalence.

 \textbf{Proof}:
 For each $y : A$, let $\defineH {\fiberH {y}{A}}{\comprehensionH {x}{A}{\equalH {x}{y}}}$ be its fiber with respect to $\idMapH {A}$ and let $\defineH {\barH {y}}{\typingH {\pairH {y}{\reflexivityH {A}{y}}}{\fiberH {y}{A}}}$.
 As for all $y : A$, $\equalH {\pairH {y}{\reflexivityH {A}{y}}}{y}$, we may apply Id-induction on $y$, $\typingH {x}{A}$ and $\typingH {z}{\idPropH {x}{y}}$ to get that \[\equalH {\pairH {x}{z}}{y}\].
 Hence, for $y : A$, we may apply $\Sigma$ -elimination on $\typingH {u}{\fiberH {y}{A}}$ to get that $\equalH {u}{y}$, so that $\fiberH {y}{A}$ is contractible.
 Thus, $\typingH {\idMapH {A}}{\arrowH {A}{A}}$ is an equivalence.
  $\Box$

 \textbf{Corollary}:
 If $U$ is a type universe, then, for $X , Y : U$, \[(*)\arrowH {\equalH {X}{Y}}{\equivalenceH {X}{Y}}\].

 \textbf{Proof}:
 We may apply the lemma to get that for $X : U$, $\equivalenceH {X}{X}$.
 Hence, we may apply Id-induction on $\typingH {X , Y}{U}$ to get that $(*)$.
  $\Box$


 \textbf{Definition}:
 A type universe $U$ is univalent, if for $X , Y : U$, the map $\equivalenceMapH {X}{Y}: \arrowH {\equalH {X}{Y}}{\equivalenceH {X}{Y}}$ in $(*)$ is an equivalence.
\end{figure}

cubicalTT parses the following.  We note an idealization : that agda supports ananymous pattern matching, so 
\codeword{\\ ( ( b , refl )}  would not typecheck in the original cubicalTT. Additionally, the reflexivity constructor is only present when the identity is inductively defined, as it is a primitive in cubical type theories.

\begin{figure}[H]
id ( a : Set ) : a -> a = \\ ( b : a ) -> b
isContr ( a : Set ) : Set = ( b : a ) * ( x : a ) -> a b == x
fiber ( a b  : Set ) ( f : a -> b ) ( y : b )  : Set = ( x : a ) * ( x : a ) -> b y == ( f x )
isEquiv ( a b  : Set ) ( f : a -> b )   : Set = ( y : b ) -> isContr ( fiber a b f y )
  where fiber ( a b  : Set ) ( f : a -> b ) ( y : b )  : Set = ( x : a ) * ( x : a ) -> b y == ( f x )
equiv ( a b : Set ) : Set = ( f : a -> b ) * isEquiv a b f

idIsEquiv ( a : Set ) : isEquiv a a ( id a ) =  ( ybar , lemma0 )
  where
    idFib : Set = fiber a a id y
    ^ ybar : idFib = ( y , refl )
    ^ lemma0 ( x : idFib ) : ( ( p ) ybar == x ) = \\ ( ( b , refl ) : ( c : a ) * ( a c == c ) ) -> refl

idIsEquiv ( x : Set ) : equiv x x = ( id , idIsEquiv x )
eqToIso ( a b : Set ) : ( Set a == b ) -> equiv a b = split refl -> idIsEquiv a
\end{figure}

We compare two abstract syntax trees side by side to show that 
