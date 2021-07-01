\section{HoTT Proofs}

\subsection{Why HoTT for natural language?}

We note that all natural language definitions, theorems, and proofs are copied
here verbatim from the HoTT book.  This decision is admittedly arbitrary, but
does have some benefits.  We list some here : 

\begin{itemize}[noitemsep]

\item As the HoTT book was a collaborative effort, it mixes the language of
many individuals and editors, and can be seen as more ``linguistically
neutral''

\item By its very nature HoTT is interdiscplinary, conceived and constructed by
mathematicians, logicians, and computer scientists. It therefore is meant to
interface with all these discplines, and much of the book was indeed formalized
before it was written

\item It has become canonical reference in the field, and therefore benefits
from wide familiarity

\item It is open source, with publically available Latex files free for
modification and distribution

\end{itemize}

The genisis of higher type theory is a somewhat elementary observation : that
the identity type, parameterized by an arbitrary type $A$ and indexed by
elements of $A$, can actually be built iteratively from previous identities.
That is, $A$ may actually already be an identity defined over another type
$A'$, namely $A \defeq x=_{A'} y$ where $x,y:A'$. The key idea is that this
iterating identities admits a homotpical interpretation : 

\begin{itemize}[noitemsep]

\item Types are topological spaces
\item Terms are points in these space

\item Equality types $x=_{A} y$ are paths in $A$ with endpoints $x$ and $y$ in
$A$

\item Iterated equality types are paths between paths, or continuous path
deformations in some higher path space. This is, intuitively, what
mathematicians call a homotopy.

\end{itemize}

To be explicit, given a type $A$, we can form the homotopy $p=_{x=_{A} y}q$
with endpoints $p$ and $q$ inhabiting the path space $x=_{A} y$.

Let's start out by examining the inductive definition of the identity type.  We
present this definition as it appears in section 1.12 of the HoTT book.

\begin{definition}
  The formation rule says that given a type $A:\UU$ and two elements $a,b:A$, we can form the type $(\id[A]{a}{b}):\UU$ in the same universe.
  The basic way to construct an element of $\id{a}{b}$ is to know that $a$ and $b$ are the same.
  Thus, the introduction rule is a dependent function
  \[\refl{} : \prod_{a:A} (\id[A]{a}{a}) \]
  called \define{reflexivity},
  which says that every element of $A$ is equal to itself (in a specified way).  We regard $\refl{a}$ as being the
  constant path %path\indexdef{path!constant}\indexsee{loop!constant}{path, constant}
  at the point $a$.
\end{definition}

We recapitulate this definition in Agda, and treat : 

\begin{code}[hide]
{-# OPTIONS --cubical #-}

module hott where
\end{code}

\begin{code}[hide]

module Id where

\end{code}
\begin{code}

  data _≡'_ {A : Set} : (a b : A) → Set where
    r : (a : A) → a ≡' a

\end{code}

\subsection{An introduction to equality}

There is already some tension brewing : most mathematicains have an intuition
for equality, that of an identitfication between two pieces of information
which intuitively must be the same thing, i.e. $2+2=4$. They might ask, what
does it mean to ``construct an element of $\id{a}{b}$''? For the mathematician
use to thinking in terms of sets $\{\id{a}{b} \mid a,b \in \mathbb{N} \}$ isn't
a well-defined notion. Due to its use of the axiom of extensionality, the set
theoretic notion of equality is, no suprise, extensional.  This means that sets
are identified when they have the same elements, and equality is therefore
external to the notion of set. To inhabit a type means to provide evidence for
that inhabitation. The reflexivity constructor is therefore a means of
providing evidence of an equality. This evidence approach is disctinctly
constructive, and a big reason why classical and constructive mathematics,
especially when treated in an intuitionistic type theory suitable for a
programming language implementation, are such different beasts.

In Martin-Löf Type Theory, there are two fundamental notions of equality,
propositional and definitional.  While propositional equality is inductively
defined (as above) as a type which may have possibly more than one inhabitant,
definitional equality, denoted $-\equiv -$ and perhaps more aptly named
computational equality, is familiarly what most people think of as equality.
Namely, two terms which compute to the same canonical form are computationally
equal. In intensional type theory, propositional equality is a weaker notion
than computational equality : all propositionally equal terms are
computationally equal. However, computational equality does not imply
propistional equality - if it does, then one enters into the space of
extensional type theory. 

Prior to the homotopical interpretation of identity types, debates about
extensional and intensional type theories centred around two features or bugs :
extensional type theory sacrificed decideable type checking, while intensional
type theories required extra beauracracy when dealing with equality in proofs.
One approach in intensional type theories treated types as setoids, therefore
leading to so-called ``Setoid Hell''. These debates reflected Martin-Löf's
flip-flopping on the issue. His seminal 1979 Constructive Mathematics and
Computer Programming, which took an extensional view, was soon betrayed by
lectures he gave soon thereafter in Padova in 1980.  Martin-Löf was a born
again intensional type theorist.  These Padova lectures were later published in
the "Bibliopolis Book", and went on to inspire the European (and Gothenburg in
particular) approach to implementing proof assitants, whereas the
extensionalists were primarily eminating from Robert Constable's group at
Cornell. 

This tension has now been at least partially resolved, or at the very least
clarified, by an insight Voevodsky was apparently most proud of : the
introduction of h-levels. We'll delegate these details for a later section, it
is mentioned here to indicate that extensional type theory was really ``set
theory'' in disguise, in that it collapses the higher path structure of
identity types. The work over the past 10 years has elucidated the intensional
and extensional positions. HoTT, by allowing higher paths, is unashamedly
intentional, and admits a collapse into the extensional universe if so desired.
We now the examine the structure induced by this propositional equality.

\subsection{All about Identity}

We start with a slight reformulation of the identity type, where the element
determining the equality is treated as a parameter rather than an index. This
is a matter of convenience more than taste, as it delegates work for Agda's
typechecker that the programmer may find a distraction. The reflexivity terms
can generally have their endpoints inferred, and therefore cuts down on the
beauracry which often obscures code. 

\begin{code}

  data _≡_ {A : Set} (a : A) : A → Set where
    r : a ≡ a

  infix 20 _≡_

\end{code}

It is of particular concern in this thesis, because it hightlights a
fundamental difference between the lingusitic and the formal approach to proof
presentation.  While the mathematician can whimsically choose to include the
reflexivity arguement or ignore it if she believes it can be inferred, the
programmer can't afford such a laxidasical attitude. Once the type has been
defined, the arguement strcuture is fixed, all future references to the
definition carefully adhere to its specification. The advantage that the
programmer does gain however, that of Agda's powerful inferential abilities,
allows for the insides to be seen via interaction windown. 

Perhaps not of much interest up front, this is incredibly important detail
which the mathematician never has to deal with explicity, but can easily make
type and term translation infeasible due to the fast and loose nature of the
mathematician's writing. Conversely, it may make Natural Language Generation
(NLG) incredibly clunky, adhering to strict rules when created sentences out of
programs. 

[ToDo, give a GF example]

A prime source of beauty in constructive mathematics arises from Gentzen's
recognition of a natural duality in the rules for introducing and using logical
connectives. The mutually coherence between introduction and elmination rules
form the basis of what has since been labeled harmony in a deductive system.
This harmony isn't just an artifact of beauty, it forms the basis for cuts in
proof normalization, and correspondingly, evaluation of terms in a programming
langauge. 

The idea is simple, each new connective, or type former, needs a means of
constructing its terms from its constiutuent parts, yielding introduction
rules. This however, isn't enough - we need a way of dissecting and using the
terms we construct. This yields an elimantion rule which can be uniquely
derived from an inductively defined type. These elimination forms yield
induction principles, or a general notion of proof by induction, when given an
interpration in mathematics. In the non-depedent case, this is known as a
recursion principle, and corresponds to recursion known by programmers far and
wide.  The proof by induction over natural numbers familiar to mathematicians
is just one special case of this induction principle at work--the power of
induction has been recognized and brought to the fore by computer scientists.

We now elaborate the most important induction principle in HoTT, namely, the
induction of an identity type.

\begin{definition}[Version 1]

Moreover, one of the amazing things about homotopy type theory is that all of the basic constructions and axioms---all of the
higher groupoid structure---arises automatically from the induction
principle for identity types.
Recall from [section 1.12]  that this says that if % \cref{sec:identity-types}
  \begin{itemize}[noitemsep]
    \item for every $x,y:A$ and every $p:\id[A]xy$ we have a type $D(x,y,p)$, and
    \item for every $a:A$ we have an element $d(a):D(a,a,\refl a)$,
  \end{itemize}
then
  \begin{itemize}[noitemsep]
    \item there exists an element $\indid{A}(D,d,x,y,p):D(x,y,p)$ for \emph{every}
    two elements $x,y:A$ and $p:\id[A]xy$, such that $\indid{A}(D,d,a,a,\refl a)
    \jdeq d(a)$.
  \end{itemize}
\end{definition}
The book then reiterates this definition, with basically no natural language,
essentially in the raw logical framework devoid of anything but dependent
function types.
\begin{definition}[Version 2]
In other words, given dependent functions
\begin{align*}
  D & :\prod_{(x,y:A)}(x= y) \; \to \; \type\\
  d & :\prod_{a:A} D(a,a,\refl{a})
\end{align*}
there is a dependent function
\[\indid{A}(D,d):\prod_{(x,y:A)}\prod_{(p:\id{x}{y})} D(x,y,p)\]
such that
\begin{equation}\label{eq:Jconv}
\indid{A}(D,d,a,a,\refl{a})\jdeq d(a)
\end{equation}
for every $a:A$.
Usually, every time we apply this induction rule we will either not care about the specific function being defined, or we will immediately give it a different name.

\end{definition}
Again, we define this, in Agda, staying as true to the syntax as possible.
\begin{code}

  J : {A : Set}
      → (D : (x y : A) → (x ≡ y) →  Set)
      → ((a : A) → (D a a r )) -- → (d : (a : A) → (D a a r ))
      → (x y : A)
      → (p : x ≡ y)
      ------------------------------------
      → D x y p
  J D d x .x r = d x

\end{code}

It should be noted that, for instance, we can choose to leave out the $d$ label
on the third line. Indeed minimizing the amount of dependent typing and using
vanilla function types when dependency is not necessary, is generally
considered ``best practice'' Agda, because it will get desugared by the time it
typechecks anyways. For the writer of the text; however, it was convenient to
define $d$ once, as there are not the same constraints on a mathematician
writing in latex. It will again, serve as a nontrivial exercise to deal with
when specifying the grammar, and will be dealt with later [ToDo add section].
It is also of note that we choose to include Martin-Löf's original name $J$, as
this is more common in the computer science literature.

Once the identity type has been defined, it is natural to develop an ``equality
calculus'',  so that we can actually use it in proof's, as well as develop the
higher groupoid structure of types. The first fact, that propositional equality
is an equivalence relation, is well motivated by needs of practical theorem
proving in Agda and the more homotopically minded mathematician. First, we show the symmetry of equality--that paths are reversible.

\begin{lem}\label{lem:opp}
  For every type $A$ and every $x,y:A$ there is a function
  \begin{equation*}
    (x= y)\to(y= x)
  \end{equation*}
  denoted $p\mapsto \opp{p}$, such that $\opp{\refl{x}}\jdeq\refl{x}$ for each $x:A$.
  We call $\opp{p}$ the \define{inverse} of $p$.
  %\indexdef{path!inverse}%
  %\indexdef{inverse!of path}%
  %\index{equality!symmetry of}%a
  %\index{symmetry!of equality}%
\end{lem}

\begin{proof}[First proof]
  Assume given $A:\UU$, and
  let $D:{\textstyle\prod_{(x,y:A)}}(x= y) \; \to \; \type$ be the type family defined by $D(x,y,p)\defeq (y= x)$.
  %$\prod_{(x:A)} \prod_{y:B}$
  In other words, $D$ is a function assigning to any $x,y:A$ and $p:x=y$ a type, namely the type $y=x$.
  Then we have an element
  \begin{equation*}
    d\defeq \lambda x.\ \refl{x}:\prod_{x:A} D(x,x,\refl{x}).
  \end{equation*}
  Thus, the induction principle for identity types gives us an element
  $\indid{A}(D,d,x,y,p): (y= x)$
  for each $p:(x= y)$.
  We can now define the desired function $\opp{(\blank)}$ to be 
  $\lambda p.\ \indid{A}(D,d,x,y,p)$, 
  i.e.\ we set 
  $\opp{p} \defeq \indid{A}(D,d,x,y,p)$.
  The conversion rule [missing reference] %rule~\eqref{eq:Jconv} 
  gives $\opp{\refl{x}}\jdeq \refl{x}$, as required.
\end{proof}
The Agda code is certainly more brief: 
\begin{code}

  _⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
  _⁻¹ {A} {x} {y} p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = y ≡ x
      d : (a : A) → D a a r
      d a = r

  infixr 50 _⁻¹

\end{code}

While first encountering induction principles can be scary, they are actually
more mechanical than one may think. This is due to the the fact that they
uniquely compliment the introduction rules of an an inductive type, and are
simply a means of showing one can ``map out'', or derive an arbitrary type
dependent on the type which has been inductively defined. The mechanical nature
is what allows for Coq's induction tactic, and perhaps even more elegantly,
Agda's pattern matching capabilities. It is always easier to use pattern
matching for the novice Agda programmer, which almost feels like magic.
Nonetheless, for completeness sake, the book uses the induction principle for
much of Chapter 2. And pattern matching is unique to programming languages,
its elegance isn't matched in the mathematicians' lexicon.

Here is the same proof via ``natural language pattern matching'' and Agda
pattern matching:

\begin{proof}[Second proof]
  We want to construct, for each $x,y:A$ and $p:x=y$, an element $\opp{p}:y=x$.
  By induction, it suffices to do this in the case when $y$ is $x$ and $p$ is $\refl{x}$.
  But in this case, the type $x=y$ of $p$ and the type $y=x$ in which we are trying to construct $\opp{p}$ are both simply $x=x$.
  Thus, in the ``reflexivity case'', we can define $\opp{\refl{x}}$ to be simply $\refl{x}$.
  The general case then follows by the induction principle, and the conversion rule $\opp{\refl{x}}\jdeq\refl{x}$ is precisely the proof in the reflexivity case that we gave.
\end{proof}

\begin{code}

  _⁻¹' : {A : Set} {x y : A} → x ≡ y → y ≡ x
  _⁻¹' {A} {x} {y} r = r

\end{code}

Next is trasitivity--concatenation of paths--and we omit the natural language
presentation, which is a slightly more sophisticated arguement than for
symmetry.  


\begin{code}
  _∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
  _∙_ {A} {x} {y} p {z} q = J D d x y p z q
      where
      D : (x₁ y₁ : A) → x₁ ≡ y₁ → Set
      D x y p = (z : A) → (q : y ≡ z) → x ≡ z
      d : (z₁ : A) → D z₁ z₁ r
      d = λ v z q → q

  infixl 40 _∙_
\end{code}

Putting on our spectacles, the reflexivity term serves as evidence of a
constant path for any given point of any given type. To the category theorist,
this makes up the data of an identity map. Likewise, conctanation of paths
starts to look like function composition. This, along with the identity laws
and associativity as proven below, gives us the data of a category. And we have
not only have a category, but the symmetry allows us to prove all paths are
isomorphisms, giving us a groupoid. This isn't a coincedence, it's a very deep
and fascinating articulation of power of the machinery we've so far built. The
fact the path space over a type naturally must satisfies coherence laws in an
even higher path space gives leads to this notion of types as higher groupoids.  

As regards the natural language--at this point, the bookkeeping starts to get hairy.  Paths between paths, and paths between paths between paths, these ideas start to lose geometric inutiotion. And the mathematician often fails to express, when writing $p= q$, that she is already reasoning in a path space. While clever, our brains aren't wired to do too much book-keeping.  Fortunately Agda does this for us, and we can use implicit arguements to avoid our code getting too messy.  [ToDo, add example]

We now proceed to show that we have a groupoid, where the objects are points,
the morphisms are paths. The isomorphisms arise from the path reversal.  Many
of the proofs beyond this point are either routinely made via the induction
principle, or even more routinely by just pattern matching on equality paths,
we omit the details which can be found in the HoTT book, but it is expected
that the GF parser will soon cover such examples.

\begin{code}
  iₗ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ r ∙ p
  iₗ {A} {x} {y} p = J D d x y p 
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ≡ r ∙ p
      d : (a : A) → D a a r
      d a = r

  iᵣ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ r
  iᵣ {A} {x} {y} p = J D d x y p 
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ≡ p ∙ r
      d : (a : A) → D a a r
      d a = r

  leftInverse : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ r 
  leftInverse {A} {x} {y} p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ⁻¹ ∙ p ≡ r
      d : (x : A) → D x x r
      d x = r

  rightInverse : {A : Set} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ r 
  rightInverse {A} {x} {y} p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ∙ p ⁻¹ ≡ r
      d : (a : A) → D a a r
      d a = r

  doubleInv : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
  doubleInv {A} {x} {y} p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ⁻¹ ⁻¹ ≡ p
      d : (a : A) → D a a r
      d a = r

  associativity :{A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
  associativity {A} {x} {y} {z} {w} p q r' = J D₁ d₁ x y p z w q r'
    where
      D₁ : (x y : A) → x ≡ y → Set
      D₁ x y p = (z w : A) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
      -- d₁ : (x : A) → D₁ x x r 
      -- d₁ x z w q r' = r -- why can it infer this 
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

\end{code}

When one starts to look at structure above the groupoid level, i.e., the paths between paths between paths level, some interesting and nonintuitive results emerge. If one defines a path space that is seemingly trivial, namely, taking the same starting and end points, the higherdimensional structure yields non-trivial structure. 
We now arrive at the first ``interesting'' result in this book, the Eckmann-Hilton Arguement. It says that composition on the loop space of a loop space, the second loop space, is commutitive.



\begin{definition}

Thus, given a type $A$ with a point $a:A$, we define its \define{loop space}
\index{loop space}%
$\Omega(A,a)$ to be the type $\id[A]{a}{a}$.
We may sometimes write simply $\Omega A$ if the point $a$ is understood from context.

\end {definition}


\begin{definition}
It can also be useful to consider the loop space\index{loop space!iterated}\index{iterated loop space} \emph{of} the loop space of $A$, which is the space of 2-dimensional loops on the identity loop at $a$.
This is written $\Omega^2(A,a)$ and represented in type theory by the type $\id[({\id[A]{a}{a}})]{\refl{a}}{\refl{a}}$.
\end {definition}

\begin{thm}[Eckmann--Hilton]%\label{thm:EckmannHilton}
  The composition operation on the second loop space
  %
  \begin{equation*}
    \Omega^2(A)\times \Omega^2(A)\to \Omega^2(A)
  \end{equation*}
  is commutative: $\alpha\cdot\beta = \beta\cdot\alpha$, for any $\alpha, \beta:\Omega^2(A)$.
  %\index{Eckmann--Hilton argument}%
\end{thm}

\begin{proof}
First, observe that the composition of $1$-loops $\Omega A\times \Omega A\to \Omega A$ induces an operation
\[
\star : \Omega^2(A)\times \Omega^2(A)\to \Omega^2(A)
\]
as follows: consider elements $a, b, c : A$ and 1- and 2-paths,
%
\begin{align*}
 p &: a = b,       &       r &: b = c \\
 q &: a = b,       &       s &: b = c \\
 \alpha &: p = q,  &   \beta &: r = s
\end{align*}
%
as depicted in the following diagram (with paths drawn as arrows).

[TODO Finish Eckmann Hilton Arguement]
%\[
 %\xymatrix@+5em{
   %{a} \rtwocell<10>^p_q{\alpha}
   %&
   %{b} \rtwocell<10>^r_s{\beta}
   %&
   %{c}
 %}
%\]
%Composing the upper and lower 1-paths, respectively, we get two paths $p\ct r,\ q\ct s : a = c$, and there is then a ``horizontal composition''
%%
%\begin{equation*}
  %\alpha\hct\beta : p\ct r = q\ct s
%\end{equation*}
%%
%between them, defined as follows.
%First, we define $\alpha \rightwhisker r : p\ct r = q\ct r$ by path induction on $r$, so that
%\[ \alpha \rightwhisker \refl{b} \jdeq \opp{\mathsf{ru}_p} \ct \alpha \ct \mathsf{ru}_q \]
%where $\mathsf{ru}_p : p = p \ct \refl{b}$ is the right unit law from \cref{thm:omg}\ref{item:omg1}.
%We could similarly define $\rightwhisker$ by induction on $\alpha$, or on all paths in sight, resulting in different judgmental equalities, but for present purposes the definition by induction on $r$ will make things simpler.
%Similarly, we define $q\leftwhisker \beta : q\ct r = q\ct s$ by induction on $q$, so that
%\[ \refl{b} \leftwhisker \beta \jdeq \opp{\mathsf{lu}_r} \ct \beta \ct \mathsf{lu}_s \]
%where $\mathsf{lu}_r$ denotes the left unit law.
%The operations $\leftwhisker$ and $\rightwhisker$ are called \define{whiskering}\indexdef{whiskering}.
%Next, since $\alpha \rightwhisker r$ and $q\leftwhisker \beta$ are composable 2-paths, we can define the \define{horizontal composition}
%\indexdef{horizontal composition!of paths}%
%\indexdef{composition!of paths!horizontal}%
%by:
%\[
%\alpha\hct\beta\ \defeq\ (\alpha\rightwhisker r) \ct (q\leftwhisker \beta).
%\]
%Now suppose that $a \jdeq  b \jdeq  c$, so that all the 1-paths $p$, $q$, $r$, and $s$ are elements of $\Omega(A,a)$, and assume moreover that $p\jdeq q \jdeq r \jdeq s\jdeq \refl{a}$, so that $\alpha:\refl{a} = \refl{a}$ and $\beta:\refl{a} = \refl{a}$ are composable in both orders.
%In that case, we have
%\begin{align*}
  %\alpha\hct\beta
  %&\jdeq (\alpha\rightwhisker\refl{a}) \ct (\refl{a}\leftwhisker \beta)\\
  %&= \opp{\mathsf{ru}_{\refl{a}}} \ct \alpha \ct \mathsf{ru}_{\refl{a}} \ct \opp{\mathsf{lu}_{\refl a}} \ct \beta \ct \mathsf{lu}_{\refl{a}}\\
  %&\jdeq \opp{\refl{\refl{a}}} \ct \alpha \ct \refl{\refl{a}} \ct \opp{\refl{\refl a}} \ct \beta \ct \refl{\refl{a}}\\
  %&= \alpha \ct \beta.
%\end{align*}
%(Recall that $\mathsf{ru}_{\refl{a}} \jdeq \mathsf{lu}_{\refl{a}} \jdeq \refl{\refl{a}}$, by the computation rule for path induction.)
%On the other hand, we can define another horizontal composition analogously by
%\[
%\alpha\hct'\beta\ \defeq\ (p\leftwhisker \beta)\ct (\alpha\rightwhisker s)
%\]
%and we similarly learn that
%\[
%\alpha\hct'\beta = \beta\ct\alpha.
%\]
%\index{interchange law}%
%But, in general, the two ways of defining horizontal composition agree, $\alpha\hct\beta = \alpha\hct'\beta$, as we can see by induction on $\alpha$ and $\beta$ and then on the two remaining 1-paths, to reduce everything to reflexivity.
%Thus we have
%\[\alpha \ct \beta = \alpha\hct\beta = \alpha\hct'\beta = \beta\ct\alpha.
%\qedhere
%\]
\end{proof}


[Todo, clean up code so that its more tightly correspondent to the book proof]
The corresponding agda code is below :

\begin{code}

  -- whiskering
  _∙ᵣ_ : {A : Set} → {b c : A} {a : A} {p q : a ≡ b} (α : p ≡ q) (r' : b ≡ c) → p ∙ r' ≡ q ∙ r'
  _∙ᵣ_ {A} {b} {c} {a} {p} {q} α r' = J D d b c r' a α
    where
      D : (b c : A) → b ≡ c → Set
      D b c r' = (a : A) {p q : a ≡ b} (α : p ≡ q) → p ∙ r' ≡ q ∙ r'
      d : (a : A) → D a a r
      d a a' {p} {q} α = iᵣ p ⁻¹ ∙ α ∙ iᵣ q

  -- iᵣ == ruₚ

  _∙ₗ_ : {A : Set} → {a b : A} (q : a ≡ b) {c : A} {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
  _∙ₗ_ {A} {a} {b} q {c} {r'} {s} β = J D d a b q c β
    where
      D : (a b : A) → a ≡ b → Set
      D a b q = (c : A) {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
      d : (a : A) → D a a r
      d a a' {r'} {s} β = iₗ r' ⁻¹ ∙ β ∙ iₗ s

  _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
  _⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)

  _⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
  _⋆'_ {A} {p = p} {s = s} α β =  (p ∙ₗ β) ∙ (α ∙ᵣ s)

  Ω : {A : Set} (a : A) → Set
  Ω {A} a = a ≡ a

  Ω² : {A : Set} (a : A) → Set
  Ω² {A} a = _≡_ {a ≡ a} r r 

  lem1 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r)
  lem1 a α β = r

  lem1' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡  (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)
  lem1' a α β = r

  -- ap\_
  apf : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
  apf {A} {B} {x} {y} f p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = {f : A → B} → f x ≡ f y
      d : (x : A) → D x x r
      d = λ x → r 

  ap : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
  ap f r = r

  lem20 : {A : Set} → {a : A} → (α : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ α
  lem20 α = iᵣ (α) ⁻¹

  lem21 : {A : Set} → {a : A} → (β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ β
  lem21 β = iᵣ (β) ⁻¹

  lem2 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ (α ∙ β)
  lem2 {A} a α β = apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

  lem2' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ (β ∙ α )
  lem2' {A} a α β =  apf  (λ - → - ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)) (lem21 β) ∙ apf (λ - → β ∙ -) (lem20 α)
  -- apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

  ⋆≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (α ∙ β)
  ⋆≡∙ a α β = lem1 a α β ∙ lem2 a α β

  -- proven similairly to above 
  ⋆'≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡ (β ∙ α)
  ⋆'≡∙ a α β = lem1' a α β ∙ lem2' a α β


  --eckmannHilton : {A : Set} → (a : A) → (α β : Ω² {A} a) → α ∙ β ≡ β ∙ α 
  --eckmannHilton a r r = r

\end{code}

[TODO, fix without k errors]

