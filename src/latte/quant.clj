(ns latte.quant
  "Basic definitions and theorems about the universal
  and existential quantifiers.

  Note that for the universal quantifier, it is a primitive of the
  calculus of constructions, hence Latte.

  The elimination rule for ∀ (for all) is application, and introduction
  is through lambda-abstraction."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation proof
                                          forall ==>
                                          assume have]]

            [latte.prop :as p :refer [and]]
            [latte.equal :as eq :refer [equal]]))

(definition ex
  "The encoding for the existential quantifier.

`(ex T P)` encodes the existential quantification

> there exists an element of type `T` such that the predicate
> `P` holds for this element.

Remark: this is a second-order, intuitionistic definition that
 is more general than the definition in classical logic.
"
  [[T :type] [P (==> T :type)]]
  (forall [α :type]
    (==> (forall [x T] (==> (P x) α))
         α)))

(defnotation exists
  "The existential quantification  `(exists [x T] P)`
 is a shortcut for `(ex T (lambda [x T] P))`, corresponding
 to the usual notation for existential quantification: ∃x:T.(P x)

> there exists an `x` of type `T` such that `(P x)` is true."
  [bindings body]
  [:ok (list '∃ bindings body)])

(alter-meta! #'exists update-in [:style/indent] (fn [_] [1 :form :form]))

(defthm ex-elim
  "The (intuitionistic) elimination rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [A :type]]
  (==> (ex T P)
       (forall [x T] (==> (P x) A))
       A))

(proof ex-elim :script
  (assume [H1 (ex T P)
           H2 (forall [x T] (==> (P x) A))]
    (have a (==> (forall [x T] (==> (P x) A))
                 A) :by (H1 A))
    (have b A :by (a H2))
    (qed b)))

(defthm ex-intro
  "The introduction rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [x T]]
  (==> (P x)
       (ex T P)))

(proof ex-intro :script
  (assume [H (P x)
           A :type
           y (forall [z T] (==> (P z) A))]
    (have a (==> (P x) A) :by (y x))
    (have b A :by (a H))
    (have c (==> (forall [z T] (==> (P z) A))
                 A) :discharge [y b])
    (have d (forall [A :type]
              (==> (forall [z T] (==> (P z) A))
                   A)) :discharge [A c])
    (qed d)))

(definition single
  "The constraint that \"there exists at most\"..."
  [[T :type] [P (==> T :type)]]
  (forall [x y T]
    (==> (P x)
         (P y)
         (equal T x y))))

(definition unique
  "The constraint that \"there exists a unique\" ..."
  [[T :type] [P (==> T :type)]]
  (and (ex T P)
       (single T P)))

(defaxiom the
  "The unique element descriptor.

  `(the T P u)` defines the unique inhabitant of type
 `T` satisfying the predicate `P`. This is provided
 thanks to the uniqueness proof `u` (of type `(unique T P)`.
"
  [[T :type] [P (==> T :type)] [u (unique T P)]]
  T)

(defaxiom the-prop
  "The property of the unique element descriptor."
  [[T :type] [P (==> T :type)] [u (unique T P)]]
  (P (the T P u)))

(defthm the-lemma
  "The unique element is ... unique."
  [[T :type] [P (==> T :type)] [u (unique T P)]]
  (forall [y T]
    (==> (P y)
         (equal T y (the T P u)))))

(proof the-lemma :script
  (have a (single T P) :by (p/%and-elim-right u))
  (have b (P (the T P u)) :by (the-prop T P u))
  (assume [y T
           Hy (P y)]
    (have c (==> (P y)
                 (P (the T P u))
                 (equal T y (the T P u))) :by (a y (the T P u)))
    (have d (equal T y (the T P u)) :by (c Hy b))
    (have e _ :discharge [Hy d])
    (have f _ :discharge [y e]))
  (qed f))

