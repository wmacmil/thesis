\subsection{What is Equality?} \label{e}

\begin{displayquote}
... the univalence axiom validates the common, but formally unjustified, practice
of identifying isomorphic objects. \emph{HoTT Book} \cite{theunivalentfoundationsprogram-homotopytypetheory-2013}
\end{displayquote}

Mathematicians have an intuition for equality, that of an identification between
two pieces of information which naturally are be indiscernible. The
philosophically inclined might ponder identification generally. We showcase
different notions of identifying things in mathematics, logic, and type theory :

\begin{itemize}
\item Equivalence of propositions
\item Equality of sets
\item Equality of members of sets
\item Isomorphism of structures
\item Equality of terms
\item Equality of types
\end{itemize}

While there are notions of equality, sameness, or identification outside of
these formal domains, we don't dare take a philosophical stab at these notions
here. We have discussed judgemental and propositional equality. Judgmental
equality is the means of computing, for instance, that $2+2=4$, for there is no
way of proving this other than appealing to the definition of addition.
Propositional equality, on the other hand, is actually a type. It is defined as
follows in Agda, with an accompanying natural language definition from \cite{theunivalentfoundationsprogram-homotopytypetheory-2013} :

\begin{code}[hide]
module equality where
\end{code}
\begin{code}
  data _≡'_ {A : Set} : (a b : A) → Set where
    r : (a : A) → a ≡' a
\end{code}
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

The astute reader might ask, what does it mean to ``construct an element of
$\id{a}{b}$''? For the mathematician use to thinking in terms of sets
$\{\id{a}{b} \mid a,b \in \mathbb{N} \}$ isn't a well-defined notion. Due to its
use of the axiom of extensionality, the set theoretic notion of equality is, no
suprise, extensional. This means that sets are identified when they have the
same elements, and equality is therefore external to the notion of set. To
inhabit a type means to provide evidence for that inhabitation. The reflexivity
constructor is therefore a means of providing evidence of an equality. This
evidentiary approach is disctinctly constructive, and is a significant reason
why classical and constructive mathematics, especially when treated in an
intuitionistic type theory suitable for a programming language implementation,
are such different beasts.

While propositional equality is inductively defined as a type, definitional
equality, denoted $-\equiv -$ and perhaps more aptly named computational
equality, is familiarly what most people think of as equality. Namely, two terms
which compute to the same canonical form are computationally equal. In
intensional type theory, propositional equality is a weaker notion than
computational equality : all propositionally equal terms are computationally
equal. However, computational equality does not imply propistional equality - if
it does, then one enters into the space of extensional type theory.

Prior to the homotopical interpretation of identity types, debates about
extensional and intensional type theories centred around two properties :
extensional type theory sacrificed decideable type checking, while intensional
type theories required extra beauracracy when dealing with equality in proofs.
This approach in intensional type theories interpreted types as setoids, leading
to ``Setoid Hell''. These debates reflected Martin-Löf's flip-flopping on the
issue. His seminal 1979 Constructive Mathematics and Computer Programming, which
took an extensional view, was soon betrayed by Martin-Löf's decision in 1986 to
become a born again intensional type theorist. His intensional dispoition was
adopted by those in Göteborg who were implementing Agda's ancestors, whereas the
extensionalists were primarily emanating from Robert Constable's group at
Cornell developing NuPrl \cite{nuprl}.

This tension has now been at least partially resolved, or at the very least
clarified, by an insight Voevodsky was apparently most proud of : the
introduction of h-levels. We'll delegate these details to more advanced
references, it is mentioned here to indicate that extensional type theory was
really ``set theory'' in disguise, in that it collapses the higher path
structure of identity types. The work over the past 10 years has elucidated the
intensional and extensional positions. HoTT, by allowing higher paths, is
unashamedly intensional, and admits a collapse into the extensional universe if
so desired. We now the examine grammars which are based of these higher type
theories.
