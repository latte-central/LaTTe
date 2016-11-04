
# A Logician's Dream

Mathematical logic is concerned with the formal specification and reasoning about mathematical content.
A proof assistant, such as LaTTe, can be seen as an implementation of a mathematical logic on a computer.

## On mathematical content

LaTTe supports four main forms of  *mathematical content*:

  - **definitions** of mathematical concepts,
  
  - statements of **axioms** asserting fundamental properties of defined concepts,

  - statements of **theorems** asserting expected logical properties of defined concepts,
  
  - together with their **proofs**: certificates that the theorems are, indeed, true,
  
(LaTTe also supports the notion of **specials** that cannot really be assimilated to
mathematical content, but rather as a bridge between mathematics and informatics).

An example of a **definition** is the notion of a surjective function:

> A function F:T->U is **surjective** if forall y in U, exists x in T such that (F x) = y.

In LaTTe this is defined as [[latte.rel/surjective]], which we reproduce below :

```clojure
(definition surjective
  "A surjective function."
  [[T :type] [U :type] [F (==> T U)]]
  (forall [y U] (exist [x T] (equal U (F x) y))))
```

Apart from being more formal, the LaTTe definition appears as quite faithful to the
 common definition (and important difference is the use of types and not (directly) sets,
  which will be discussed below).
  
An example of an **axiom** (namely of Peano arithmetics) follows:

> The successor function on integers is bijective.

In LaTTe such an axiom can be stated as follows:

```clojure
(defaxiom succ-bijective
  "The successor function is bijective."
  []
  (rel/bijective int int succ))
```

(cf. [[latte.rel/bijective]])

Based on a set of basic axioms and defined concepts, the working mathematician's routine is to state
theorems and provide proofs of such theorems. This is also, of course, the routine of the LaTTe used.

Here is an example of a theorem:

> The successor function is surjective.

This is stated as follows in LaTTe:

```clojure
(defthm succ-surjective
  "The successor function is surjective."
  []
  (rel/surjective int int succ))
```

The proof for this theorem is of course trivial.

> We now by an axiom that the successor function is bijective, hence it
> is also surjective (and injective). Qed.

In LaTTe, this simple proof can also be expressed, e.g. as follows:

```clojure
(proof succ-surjective :term
  ((rel/bijective-is-surjective int int succ) succ-bijective))
```

This can be interpred as follows:

> The proof of the theorem [[latte.rel/bijective-is-surjective]] is a function
> that takes some `proof-of-bijection-for-...` as a parameter, and deduces that
> this `proof-of-bijection-for-...` is also a `proof-of-surjection-for-...`. This
> proof is applied to the axiom `succ-bijective` to yield the expected result.

The last form of mathematical content available is a notion of a library,
 book or theory, allowing to regroup a set of definitions, axioms, theorems
  and proofs under a common name (e.g. *group theory*, *graph theory*, etc.).
Latte here only exploit the Clojure programming environment, where the primary
 feature is called a namespace (but there is also a powerful notion of
  deployable library based on the JVM ecosystem).

## The mathematical notation

During the centuries of the development of mathematics, a complex (more or less) formal notation
has been developped.

Advantage: all the mathematical literature is based on this notation

Drawback: it is not completely formal, and its support on a computer is difficult

A primary functionality of a proof assistant is to encode mathematical content so that
 it is "understood" by the computer. Many proof assistant accept a language
  very close to the common mathematical notation. It cannot be the same because many
   ambiguities and such must be solved to match the level of formality required
    by a computing environment. This is the infamous *parsing* problem, which
    is in fact a difficult problem.

A clearly controversial but totally assumed choice of LaTTe is to adopt a programming language
 notation instead of a mathematical one. The immediate advantage is that the parsing problem
  becomes trivial, it is performed by the programming language itself ! This is the Lisp way
   of seing things, which is conveyed (and improved) by the Clojure language.
   
TODO exemple en maths, équivalent en LaTTe.


## Informal vs. formal reasoning

The language of mathematics is highly codified and makes use of many symbols, but it is still
 mostly informal. In a way, the language used for describing and reasoning about the obviously highly formal concepts
 of mathematics is itself rather ... informal. Mathematical logics aims at a better, more formal, 
 notion of "a language of mathematics". If philosophers approached this problem already centuries ago, the
  most important developments had to wait for a sufficent development of mathematics itself. Here follow some
   important events, dates and people involved in the problematic.
   
   - boole
   - cantor
   - fregge
   - principia mathematica
   - zermelo frankael and set theory
   - Church lambda-calculus and theory of types
   - Curry-Howard, Per Martin Lof
   - LCF
   - System F (Girard/Reynolds)
   - Calculus of Constructions (Coquand/Huet)
   
LaTTe is, similarly to other proof assitants, a computer-based environment for formalizing and reasoning
about mathematical content. It is thus an answer to the problem at hand, and a particularly good
answer in that it is difficult to be more formal (and stubborn) than a computer !

Technically-speaking, LaTTe implements a lambda-calculus that is
close to the calculus of constructions.  It is more precisely a variant of *lambdaD* 
(as defined in the book *Type Theory and Formal Proofs*), i.e. a variant of the calculus of constructions 
extended with definitional features.

There is still some place for informalities:

  - the explanations around the formal definitions and proofs,
  
  - the justification of the axioms
  
The latter is such an important aspect that it is the thema of the next section.

## Axioms vs. Theorems

There is a centuries-long debate about the acceptance or rejection of *axioms* in many mathematical
 theories. Some axioms are clearly beyond discussion (e.g. the axioms of ZF set theory, the axioms
  of Peano arithmetics, etc.) and some axioms are (still) heavily debated (choice or not choice,
   classical or not, cf. below, etc.).
Introducing an axiom should thus be a very careful decision, and most importantly, it must
be justified by a mathematical (if not philosophical) argument.

This is a first important distinction between an axiom and a theorem:

 - an axiom is justified by an informal mathematical/philosophical argument
 
 - a theorem is justified by a formal proof

Using LaTTe, nothing prevents the replacement of all theorems by corresponding axioms. In fact,
 we can simply replace `defthm` (definition of a theorem) by `defaxiom` and remove all the proofs.
However, what we end up with is not very satisfying.

 - an axiom can introduce an inconsistencies, whereas a theorem cannot
 
 - an axiom having no proof, having only axioms means there are no proofs anymore,
   hence we fail at the formalization of reasoning. There is no reasoning anymore !
   
Hence the way most people do mathematics is:

  - to rely on a minimal set of thoroughly (albeit informally) justified axioms
  
  - state and prove theorems whenever possible.
  
The "parti-pris" of LaTTe is to have no fear of axioms, as long as they are *mathematical
 folklore*. For example, we have nothing to fear about the Peano axioms of integer arithmetic.
 And we have no fear of the *law (axiom) of the excluded middle*, but this is an important
  topic so let's open a next section.

## Classical vs. Intuitionistic

Classical reasoning abunds in the mathematics literature.

Some guidelines:

  - when classical reasoning is the simplest, don't be shy
  
  - if a constructive proof is available, and it is not extremely complex
   if compared to a classical one, then it is to be favored.
   
The intuitionistic objective of trying to be "constructive only", and reject
 the excluded middle, could be pursued in LaTTe (it suffices not to rely on
  the [[excluded-middle]] axiom). But this is not the objective
 pursued by its authors and the "standard" library.

TODO

## Types vs. Sets

The *typed vs. untyped* debate is a class thema of programming languages. For example,
 the Clojure is strongly (everything has a type), dynamically (type-checking is performed
  at runtime) typed. A language such as ML is strongly and statically typed, because
  type-checking is perfomed at compile-time. Note that finding a truely "untyped" language
   is not easy (maybe tcl or bash because everything is a string at first ?).
There is a related, although distinct, debate between typed and untyped mathematical theories.

For example, the ZF set theory that serve as the "true" foundations for mathematics (this is what's
accepted by many if not all mathematicians) is indeed untyped. A set has no type, it is just
 a collection of elements with some (axiomatic) constraints (e.g. the foundation axiom ensures
  that a set cannot be contained in itself).  Types were mostly developed in a mathematical
   setting for the very problem we are concerned with: the formalization of mathematical
    reasoning.
	
We have no strong opinion to defend but it is important to know that LaTTe, being based
 on a typed lambda-calculus is, of course, a type theory. Hence it is *not* based on the
 accepted foundations of mathematics, but relies on an typed alternative. One informal
  argument that may justify this choice (beyond the beauty of the approach from a
  computer science point of view) is that in everyday mathematical practice many
   concepts are informally typed: "consider a set E of integers, etc."
  
Note that sets are not completely eliminated from the theory. An expressive notion
 of typed set can be formulated as a predicate over a type: "the (sub)set of elements
  of a given type that satisfy a given property" e.g. the subset Nat of the type Int.
Many developments of set theory can be restated in this *subset* setting.

## Dependent vs. non-dependent types

TODO
