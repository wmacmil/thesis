\begin{code}[hide]

-- {-# OPTIONS --omega-in-omega --type-in-type #-}

module nproof where

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_+_) public
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

ℕrec : {X : Set} -> (ℕ -> X -> X) -> X -> ℕ -> X
ℕrec f x zero = x
ℕrec f x (suc n) = f n (ℕrec f x n)

natrec : {X : Set} → ℕ → X → (ℕ → X → X) → X
natrec zero e₀ e₁ = e₀
natrec (suc n) e₀ e₁ = e₁ n (natrec n e₀ e₁)

-- natind : {X : ℕ → Set} → (n : ℕ) → X zero → ((n : ℕ) → X n → X (suc n)) → X n
-- natind zero base step = base
-- natind (suc n) base step = step n (natind n base step)
natind : {C : ℕ -> Set} -> C zero -> ((n : ℕ) -> C n -> C (suc n)) -> (n : ℕ) -> C n
natind base step zero     = base
natind base step (suc n) = step n (natind base step n)
\end{code}

\begin{code}
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc x + n = suc (x + n)

2+2=4 : 2 + 2 ≡ 4
2+2=4 = refl
\end{code}
\begin{code}[hide]
infixl 6 _+_

postulate
  roadblockn : ∀ (m : ℕ) → m + zero ≡ m -- identity cancels on the left
roadblock = λ (n : ℕ) → roadblockn n

variable
  A B : Set
  a a' : A
\end{code}

We now present the type which encodes the proposition which says $0$
plus some number is propositionally equal to that number. Agda is able to
compute evidence for this proposition via the definition of addition, and
therefore reflexivly know that number is equal to itself. Yet, the novice
Agda programmer will run into a \term{roadblock}: the proposition that any number
added to $0$ is not definitionally equal to $n$, i.e. that the defining
equations don't give an automatic way of universally validating this fact about
the second arguement. This is despite the fact that given any number, like $3+0$,
Agda can normalize it to $3$.

\begin{code}
0+n=n : ∀ (n : ℕ) → 0 + n ≡ n
0+n=n n = refl

3+0=n : 3 + 0 ≡ 3
3+0=n = refl

n+0=n : ∀ (n : ℕ) → n + 0 ≡ n
n+0=n = roadblock
\end{code}

To overcome the \term{roadblock}, one must use induction, which we show here by
pattern matching. We use an auxiliary lemma \term{ap} which says that all
functions are well defined with respect to propositional equality. Then we can
simply use \term{ap} applied the successor function and the induction hypothesis
which manifests 5s a simple recursive call. This proof is actually, verabatim,
the same as the \term{associativity-plus} proof - which gives us one perspective that
suggests, at least sometimes, types can be even more expressive than programs in
Agda.

\begin{code}
ap : (f : A → B) → a ≡ a' → f a ≡ f a'
ap f refl = refl

n+0=n' : ∀ (n : ℕ) → n + 0 ≡ n
n+0=n' zero = refl
n+0=n' (suc n) = ap suc (n+0=n' n)

associativity-plus : (n m p : ℕ) → ((n + m) + p) ≡ (n + (m + p))
associativity-plus zero m p = refl
associativity-plus (suc n) m p = ap suc (associativity-plus n m p)
\end{code}

To construct a GF grammar which includes both the simple types as well as those
which may depend on a variable of some other type, one simply gets rid of the
syntactic distinction, whereby everything is just in \term{Exp}. We show the
dependent function in GF along with its introduction and elimination forms, noting
that we include \emph{telescopes} as syntactic sugar to not have to repeat
$\lambda$ or $\Pi$ expressions. Telescopes are lists of types which may depend
on earlier variables defined in the same telescope.

\begin{verbatim}
fun
  Pi : [Tele] -> Exp -> Exp ;    -- types
  Fun : Exp -> Exp -> Exp ;
  Lam : [Tele] -> Exp -> Exp ;   -- terms
  App : Exp -> Exp -> Exp ;
  TeleC : [Var] -> Exp -> Tele ; --telescope
\end{verbatim}

This grammar allows us to prove the above right-identity and associativity laws.
Before we look at the natural language proof generated by this code, we first
look at an idealized version, which is reproduced from the Software Foundations text
\cite{pierce2010software}.

\begin{verbatim}
Theorem: For any n, m and p,
  n + (m + p) = (n + m) + p.
Proof: By induction on n.
  First, suppose n = 0. We must show that
    0 + (m + p) = (0 + m) + p.
  This follows directly from the definition of +.
  Next, suppose n = S n', where
    n' + (m + p) = (n' + m) + p.
  We must now show that
    (S n') + (m + p) = ((S n') + m) + p.
  By the definition of +, this follows from
    S (n' + (m + p)) = S ((n' + m) + p),
  which is immediate from the induction hypothesis. Qed.
\end{verbatim}

While overly pedantic relative to a mathematicians preferred conciseness,
this illustrates a proof which is both syntactically complete and semantically
adequate. Let's compare this proof with our Agda reconstruction using
the an induction principle.

\begin{code}
associativity-plus-ind' : (n m p : ℕ) → ((n + m) + p) ≡ (n + (m + p))
associativity-plus-ind' n m p = natind baseCase (λ n₁ ih → simpl n₁ (indCase n₁ ih)) n
  where
    baseCase : (zero + m + p) ≡ (zero + (m + p))
    baseCase = refl
    indCase : (n' : ℕ) → (n' + m + p) ≡ (n' + (m + p)) →
                suc (n' + m + p) ≡ suc (n' + (m + p))
    indCase = (λ n' x → ap suc x )
    simpl : (n' : ℕ) -- we must now show that
            → suc (n' + m + p) ≡ suc (n' + (m + p))
            → (suc n' + m + p) ≡ (suc n' + (m + p))
    simpl n' x = x
\end{code}

This proof, aligned with with the text so-as to allow for idealized translation,
is actually overly complicated and unnessary for the Agda programmer. For the
proof state is maintained interactively, the definitional equalities are
normalized via the typechecker, and therefore the base case and inductive case
can be simplified considerably once the \emph{motive}, the type we are
eliminating into, is known \cite{motive}. Fortunately, Agda's pattern matching
is powerful enough to infer the motive, so that one can generally pay attention
to ``high level details" generally. We see a ``more readable" rewriting below,
with the motive given in curly braces :

\begin{code}
associativity-plus-ind : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
associativity-plus-ind m n p =
  natind {λ n' → (n' + n) + p ≡ n' + (n + p)} baseCase indCase m
  where
    baseCase = refl
    indCase = λ (n' : ℕ) (x : n' + n + p ≡ n' + (n + p)) → ap suc x
\end{code}

\paragraph{Associativity in GF} \label{appHell}

Finally, taking a ``desguared" version of the Agda proof term, as presented in
our grammar, we can can reconstruct the lambda term which would, in an ideal
world, match the Software Foundations proof.

\begin{verbatim}
p -lang=LHask "
  \\ ( n m p : nat ) ->
  natind
    (\\ (n' : nat) ->
      ((plus n' (plus m p)) == (plus (plus n' m) p)))
    refl
    ( \\ ( n' : nat ) ->
     \\ (x : ((plus n' (plus m p)) == (plus (plus n' m) p)))
      -> ap suc x )
    n" | l
------------
  function taking n , m p in the natural numbers
  to
  We proceed by induction over n .
  We therefore wish to prove : function taking n',
    in the natural numbers to apply apply plus to
    n' to apply apply plus to m to p is equal
    to apply apply plus to apply apply plus to n'
    to m to p .
  In the base case, suppose m equals zero.
    we know this by reflexivity .
  In the inductive case,
    suppose m is the successor.
    Then one has one has function taking n' ,
      in the natural numbers to function
      taking x , in apply apply plus to n'
      to apply apply plus to m to p is equal to
      apply apply plus to apply apply plus to n'
      to n' to p to apply ap to the successor
      of x.
\end{verbatim}

This is horrendous. There are a few points which make this proof non-trivial to
translate. There is little support for punctuation and proof structure - the
indentations were added by hand. The syntactic distinctions have been discharged
into a single \term{Exp} category, and therefore, terms like $0$, a noun, and
the whole proof term above (multiple sentences) are both compressed into the
semantic box. This poses a huge issue for the GF developer wishing to utilize
the RGL, whereby these grammatical categories (and therefore linearization
types) are distinct, but our abstract syntax offers an incredibly course view of
the PL syntax.

This may be overcome by creating many fields in the record \codeword{lincat} for
\term{Exp}, one for each syntactic category, i.e.
\codeword{lincat Exp = { nounField : CN ; sentenceField : S ; ...}}.
Then one may match on parameters
with functions have \term{Exp} arguements to ensure that different arguements
are compatible with the assigned resource gramamr types. This approach has been
used at Digital Grammars for a client looking to produce natural language for a
code base, but unfortunately the grammar is not publically avaialable
\cite{rantaZ}. The more expressions one has the more difficult it becomes to
define a suitable linearization scheme and generalizing it to full scale
mathematics texts with the myriad syntactic uses of different types of
mathematical terms seems intractible. Ganesalignam did invent a different
theoretical notion ``type" to cover grammartical artificats in textual
mathematics, and this may be relevant to invsetigate here.

The application function, which is so common it gets the syntactic distinction
of whitespace in programming languages, does not have the same luxury in the
natural language setting. This is because the typechecker is responsible for
determining if the function is applied to the right number of arguements, and we
have chosen a \emph{shallow embedding} in our programming language, whereby
\codeword{Plus} is a variable name and not a binary function. This can also be
reconciled at the concrete level, as was demonstrated with a relatively simple
example \cite{warrickPrec}. Nonetheless, to add this layer of complextiy to the
linearization seems unneccessarily difficult, as it would be simpler to resolve this by
somehow matching the arguement structure of the agda function to some deeply
embedded addition function, \codeword{Plus : Exp -> Exp -> Exp}. Ranta, for
example, does this in the HoTT grammar \ref{rantaHott}.

Finally, we should point out an \emph{error} : ``apply ap to the successor of x" is
incorrect. The \term{successor} is actually an arguement of \term{ap}, and isn't
applied to x directly on the final line. This is because
\codeword{Suc : Exp -> Exp} was deeply embedded into GF, and the
$\eta$-expanded version should be
substituted to correct for the error (which will make it even more unreadable).
Alternatively, one could include all permutation forms of an expression's type
signature up to $\eta$-equivalence (depending on the number of both implicit and
explicit arguements). This could make the grammar both overgenerate and also
make it significantly more complex to implement. These are relatively simple
obstacles for the PL developer where the desugaring process sends
$\eta$-equivalent expressions to some normal form, so that the programmer can be
somewhat flexible. The lack of the same freedom in natural language, however,
creates numerous obstacles for the GF developer. These are often nontrivial to
identify and reconcile, especially when one layers the complexity of multiple
natural language features covered by the same grammar.
