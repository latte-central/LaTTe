# LaTTe

http://latte-central.github.io/LaTTe/

```text
             ((((
            ((((
             ))))
          _ .---.
         ( |`---'|
          \|     |
          : .___, :
           `-----'  -Karl
```

**LaTTe** : a Laboratory for Type Theory experiments (in clojure)


[![Clojars Project](https://img.shields.io/clojars/v/latte.svg)](https://clojars.org/latte)
## What?

LaTTe is a **proof assistant library** based on type theory (a variant of
λD as described in the book [Type theory and formal proof: an introduction](http://www.cambridge.org/fr/academic/subjects/computer-science/programming-languages-and-applied-logic/type-theory-and-formal-proof-introduction)).

 - **Hot!** Watch Latte *live* at: https://www.youtube.com/watch?v=5YTCY7wm0Nw

 - **Sizzling!** A paper about LaTTe at the European Lisp Symposium, 2017:
   https://github.com/latte-central/latte-ELS-2017
   [[PDF]](https://github.com/latte-central/latte-ELS-2017/blob/master/paper/latte-els-2017.pdf)

 - **Blistering** LaTTe was in the [Hacker news!](https://news.ycombinator.com/item?id=18383654)

The specific feature of LaTTe is its design as a library (unlike most proof assistant, generally designed as tools) tightly integrated with the Clojure language. It is of course fully implemented in Clojure, but most importantly all the definitional aspects of the assistant (definitions, theorem and axioms) are handled using Clojure namespaces, definitions and macros.

For example, the fact that logical implication is reflexive can be stated *directly as a Clojure top-level form*:

```clojure
(defthm impl-refl
  "Implication is reflexive."
  [[A :type]]
  (==> A A))
;; => [:declared :theorem impl-refl]
```
in plain text:
> assuming a type `A`, then `A` implies `A`.

The proof of the theorem can be also constructed as a Clojure form:

  - either giving a lambda-term as a direct proof (exploiting the proposition-as-type, proof-as-term correspondance) :

```clojure
(proof 'impl-refl
  (qed (lambda [x A] x)))
;; => [:qed impl-refl]
```
(i.e. the identity function is a proof of reflexivity for implication)

  - or using a declarative *proof script*:

```clojure
(proof 'impl-refl
   (assume [x A]
     (have concl A :by x))
   (qed concl))
;; => [:qed impl-refl]
```

... which, with some training, can be read as a "standard" mathematical proof:

> assuming `A` holds, as an hypothesis named `x`
> we can deduce `A` by `x`
> hence `A` implies `A` as stated (QED).

Of course, all the proofs are *checked for correctness*. Without the introduction
 of an inconsistent axiom (and assuming the correctness of the implementation of the LaTTe kernel),
 *no mathematical inconsistency* can be introduced by the `proof` form.

## Yes, but what?

LaTTe helps you formalize mathematic concepts and construct formal proofs of theorems (propositions) about such concepts.
Given the tight integration with the Clojure language, *existing* Clojure development environments (e.g. Cider, Cursive) can be used as (quite effective) interactive proof assistants.

## How?

 - There will be a *tutorial* at some point ...

 - The *reference documentation* is at: http://latte-central.github.io/LaTTe/

**Standard library** :

 - The **prelude** library is at: https://github.com/latte-central/latte-prelude

 - The **(typed) sets** library is at: https://github.com/latte-central/latte-sets

 - The **integer arithmetic** library is at: https://github.com/latte-central/latte-integers

(obviously more to come ...)

## Who?

LaTTe may be of some interest for you:

  - **obviously** if you are interested in type theory and the way it can be implemented on a Computer. LaTTe has been implemented with readability and simplicity in mind (more so than efficiency or correctness),
  - **probably** if you are interested in the "mechanical" formalization of mathematics, intuitionistic logic, etc. (although you might not learn much, you may be interested in contributing definitions, theorems and proofs),
  - **maybe** if you are curious about the lambda-calculus (the underlying theory of your favorite programming language) and dependent types (a current trend) and what you can do with these besides programming.

## When?

LaTTe is, at least for now, an experiment more than a finalized product, but it is already usable.

A few non-trivial formalizations have been conducted using LaTTe:

 - e.g. a (gorilla REPL) document about **Knaster-Tarski fixed point theorem(s)**: https://github.com/latte-central/fixed-points

Contributions such as mathematical content or enhancement/correction of the underlying machinery are very much welcomed.

## Build

Running Tests

```
clj -A:test
```

Building Documentation

```
clj -A:codox
```
----
Copyright (C) 2015-2018 Frederic Peschanski (MIT license, cf. `LICENSE`)
