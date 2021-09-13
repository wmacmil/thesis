\subsection{Hott and cubicalTT Grammars} \label{comparison}

We briefly look at the code fragment from Ranta's HoTT grammar, where we compare
Peter Aczel's text, an equivalent Agda presentation, and the syntax for our
cubicalTT parser. Below is the rendered latex:

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

Following is the Agda code, where we chose names based off the original cubicalTT proofs.


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

idIsEquiv : (A : Set) → isEquiv A A (id {A})
idIsEquiv A y = ybar , fib'Contr
  where
    fib' : Set -- {y}_A
    fib' = fiber A A id y
    ybar : fib'
    ybar = y , r
    fib'Contr : (x : fib') → _≡_ {Σ A (_≡_ y)} ybar x
    fib'Contr = λ {(a , r) → r}

equiv : ( a b : Set ) → Set
equiv a b = Σ (a → b) λ f → isEquiv a b f

equivId : (x : Set) → equiv x x
equivId x = id , (idIsEquiv x)

eqToIso : ( a b : Set ) → _≡_ {Set} a b → equiv a b
eqToIso a .a r = equivId a
\end{code}

Our cubicalTT grammar parses the following:

\begin{verbatim}
id ( a : Set ) : a -> a = \\ ( b : a ) -> b

isContr ( a : Set ) : Set = ( b : a ) * ( x : a ) -> a b == x

fiber ( a b  : Set ) ( f : a -> b ) ( y : b )  : Set
  = ( x : a ) * ( x : a ) -> b y == ( f x )

isEquiv ( a b  : Set ) ( f : a -> b )   : Set
  = ( y : b ) -> isContr ( fiber a b f y )
  where fiber ( a b  : Set ) ( f : a -> b ) ( y : b )  : Set
    = ( x : a ) * ( x : a ) -> b y == ( f x )

equiv ( a b : Set ) : Set = ( f : a -> b ) * isEquiv a b f

idIsEquiv ( a : Set ) : isEquiv a a ( id a ) =  ( ybar , lemma0 )
  where
    idFib : Set = fiber a a id y
    ^ ybar : idFib = ( y , refl )
    ^ lemma0 ( x : idFib ) : ( ( p ) ybar == x )
      = \\ ( ( b , refl ) : ( c : a ) * ( a c == c ) ) -> refl

idIsEquiv ( x : Set ) : equiv x x = ( id , idIsEquiv x )

eqToIso ( a b : Set ) : ( Set a == b ) -> equiv a b
  = split refl -> idIsEquiv a
\end{verbatim}

We note an idealization in our code preventing the ``correct parse" because Agda
supports anonymous pattern matching. \codeword{\\ ( ( b , refl )} would not
type-check in the cubicalTT language. Additionally, the reflexivity constructor
is only present when the identity type is inductively defined. Cubical type theories
treat reflexivity of paths as a theorem, not a constructor. We choose to be
quite pedantic in our analysis of Aczel's text. Points of interest we include
are the following :

\begin{itemize}

\item The first definition is actually \emph{two definitions}, where \emph{the
center of contraction} is subsumed. Our cubicalTT grammar doesn't define the
center of contraction, despite the fact that it should either be in a \codeword{where}
clause or accounted for separately if it is to be referenced as such later on.

\item The second definition is actually three definitions : fiber, equivalence
and $\simeq$, or \term{fiber}, \term{isEquiv} and \term{equiv}, respectively.

\item The English proof of the lemma is wrong - some of the $y$'s should be $\barH
{y}$'s

\item We didn't include univalence in our Agda formalization because it uses
higher universes. To refactor everything to account for universes, one would
necessarily break the the cubicalTT syntactic relation with Agda.

\item The corollary is the only place in the text that explicitly includes type
universe, where it is presumed in each definition and lemma. The syntactically
complete Agda proof could used generalized variables to try to mimic this, but
we chose not to.

\item It is unclear what is the foundational attitude when Aczel says
$a$ type $A$ versus $A : U$, and if these are semantic details relevant to
Aczel's foundational system or just syntactic ways of overloading the same
concept.

\item In the proof of the lemma, applying $\Sigma$-elimination on what is
denoted set implies the $\{\_ {:} \_\}$ set comprehesion notation is actually overloaded to
mean the $\Sigma$ type.

\item In Aczel's proof of the corollary, identity induction should also include an
equality arguement.

\item The proof of the corollary doesn't mention the identity function, whereas
the syntactically complete object in Agda must make the identity map visible,
even if it is inferrable once we know we are applying the lemma.

\end{itemize}

This brief analysis showcases how much the mathematician is actually doing in
her head when she reads someone else's argument - there is certainly a lot of
explicit changes which need to be made to satisfy Agda when formalizing these
utterances and writings. Indeed, it is often impossible to tell whether an
arguement is being thorough in every small detail, because the mathematician is
not aware of the ``bureaucratic bookkeeping", while Agda strictly enforces it.

To witness how the syntactically complete and semantically adequate proofs are
different, we compare two abstract syntax trees for the \emph{contractible}
definition in \autoref{fig:I2}. On the left is our cubicalTT grammar, and
Ranta's HoTT grammar is presented on the right. We notice that:

\begin{itemize}

\item Ranta's grammar doesn't have the \codeword{cons} and \codeword{base} telescope

\item Propositions, sorts, functions, and expressions are all denoted in the
names of the nodes in Ranta's grammar, whereas the cubicalTT grammar doesn't
make these semantic distinctions.

\item cubicalTT grammar must include universe data to satisfy the type-checker

\item The center of contraction has linguistic value in Ranta's grammar, but it
isn't locally defined anywhere in the AST

\end{itemize}

Despite these differences, we could produce a cubicalTT syntax by finessing
Ranta's grammar on this example relatively simply. This demonstrates that our
syntax trees are related at least by what they are able to parse. Nonetheless,
trying compare syntax trees for even the second definition, which weren't
pictured because the details were uninformative, shows that the grammars have
fundamental differences that would pose significant challenges already to the
Haskell developer looking to translate a tree in one GF grammar to another.

\begin{figure}[H]
\centering
\begin{minipage}[t]{.5\textwidth}
\begin{verbatim}
* DeclDef
    * Contr
      ConsTele
        * TeleC
            * A
              BaseAIdent
              Univ
          BaseTele
      Univ
      NoWhere
        * Sigma
            * BasePTele
                * PTeleC
                    * Var
                        * B
                      Var
                        * A
              Pi
                * BasePTele
                    * PTeleC
                        * Var
                            * X
                          Var
                            * A
                  Id
                    * Var
                        * A
                      Var
                        * B
                      Var
                        * X
\end{verbatim}
\end{minipage}%
\begin{minipage}[t]{.55\textwidth}
\begin{verbatim}
* PredDefinition
    * type_Sort
      A_Var
      contractible_Pred
      ExistCalledProp
        * a_Var
          ExpSort
            * VarExp
                * A_Var
          FunInd
            * centre_of_contraction_Fun
          ForAllProp
            * allUnivPhrase
                * BaseVar
                    * x_Var
                  ExpSort
                    * VarExp
                        * A_Var
              ExpProp
                * DollarMathEnv
                  equalExp
                    * VarExp
                        * a_Var
                      VarExp
                        * x_Var
\end{verbatim}
\end{minipage}
\caption{Mathematical Assertions and Agda Judgments} \label{fig:I2}
\end{figure}
