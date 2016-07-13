(ns latte.quant
  "Basic definitions and theorems about the universal
  and existential quantifiers.

  Note that for the universal quantifier, it is a primitive of the
  calculus of constructions, hence Latte.

  The elimination rule for ∀ (for all) is application, and introduction
  is through lambda-abstraction."

  (:require [latte.core :as latte :refer [definition defthm proof forall exist
                                          assume have]])
  )


(definition ex
  "The encoding for the existential quantifier.

`(ex T P)` encodes the existential quantification

> there exists an element of type `T` such that the predicate
> `P` holds for this element.

Remark: this is a second-order, intuitionistic definition that
 is more general than the definition in classical logic.

Based on this encoding, one can use the syntax `(exists [x T] P)`
 which is a shortcut for `(ex T (lambda [x T] P))`, corresponding
 to the usual notation for existential quantification: ∃x:T.(P x)

> there exists an `x` of type `T` such that `(P x)` is true.
"
  [[T :type] [P (==> T :type)]]
  (forall [α :type]
    (==> (forall [x T] (==> (P x) α))
         α)))

(defthm exist-elim
  "The (intuitionistic) elimination rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [A :type]]
  (==> (ex T P)
       (forall [x T] (==> (P x) A))
       A))

(proof exist-elim :script
  (assume [H1 (ex T P)
           H2 (forall [x T] (==> (P x) A))]
    (have a (==> (forall [x T] (==> (P x) A))
                 A) :by (H1 A))
    (have b A :by ((a) H2))
    (qed b)))

(defthm exist-intro
  "The introduction rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [x T]]
  (==> (P x)
       (ex T P)))

(proof exist-intro :script
  (assume [H (P x)
           A :type
           y (forall [z T] (==> (P z) A))]
    (have a (==> (P x) A) :by (y x))
    (have b A :by ((a) H))
    (have c (==> (forall [z T] (==> (P z) A))
                 A) :discharge [y (b)])
    (have d (forall [A :type]
              (==> (forall [z T] (==> (P z) A))
                   A)) :discharge [A (c)])
    (qed d)))

