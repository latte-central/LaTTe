(ns latte.equal
  "The formal definition of equality, and its basic properties."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defthm forall assume have proof]])

  (:require [latte.prop :as p :refer [<=> and or not]])
  )

(definition equal
  "The intuitionistic, second-order definition of equality.
This corresponds to Leibniz's *indiscernibility of identicals*."
  [[T :type] [x T] [y T]]
  (forall [P (==> T :type)]
    (<=> (P x) (P y))))

(defthm eq-refl
  "The reflexivity property of equality."
  [[T :type] [x T]]
  (equal T x x))

(proof eq-refl :script
  (assume [P (==> T :type)]
    (have a (<=> (P x) (P x)) :by (p/iff-refl (P x)))
    (qed a)))

(defthm eq-sym
  "The symmetry property of equality."
  [[T :type] [x T] [y T]]
  (==> (equal T x y)
       (equal T y x)))

(proof eq-sym :script
  (assume [Heq (equal T x y)
           P (==> T :type)]
    (have a (<=> (P x) (P y)) :by (Heq P))
    (have b (<=> (P y) (P x)) :by ((p/iff-sym (P x) (P y)) a))
    (have c _ :discharge [P b])
    (qed c)))

(defthm eq-trans
  "The transitivity property of equality."
  [[T :type] [x T] [y T] [z T]]
  (==> (equal T x y)
       (equal T y z)
       (equal T x z)))

(proof eq-trans :script
  (assume [H1 (equal T x y)
           H2 (equal T y z)
           P (==> T :type)]
    (have a (<=> (P x) (P y)) :by (H1 P))
    (have b (<=> (P y) (P z)) :by (H2 P))
    (have c (<=> (P x) (P z))
          :by ((p/iff-trans (P x) (P y) (P z)) a b))
    (have d _ :discharge [P c])
    (qed d)))

(defthm eq-subst
  "Substitutivity property of equality."
  [[T :type] [P (==> T :type)] [x T] [y T]]
  (==> (equal T x y)
       (P x)
       (P y)))

(proof eq-subst :script
  (assume [H1 (equal T x y)
           H2 (P x)]
    (have a (<=> (P x) (P y)) :by (H1 P))
    (have b (P y) :by ((p/iff-elim-if (P x) (P y)) a H2))
    (qed b)))

(defthm eq-cong
  "Congruence property of equality."
  [[T :type] [U :type] [f (==> T U)] [x T] [y T]]
  (==> (equal T x y)
       (equal U (f x) (f y))))

(proof eq-cong :script
  (assume [H1 (equal T x y)
           Q (==> U :type)]
    (assume [H2 (Q (f x))]
      (have a1 _ :by (eq-subst T (lambda [z T] (Q (f z))) x y))
      (have a2 (Q (f y)) :by (a1 H1 H2))
      (have a (==> (Q (f x)) (Q (f y))) :discharge [H2 a2]))
    (have b (equal T y x) :by ((eq-sym T x y) H1))
    (assume [H3 (Q (f y))]
      (have c1 _ :by (eq-subst T (lambda [z T] (Q (f z))) y x))
      (have c2 (Q (f x)) :by (c1 b H3))
      (have c (==> (Q (f y)) (Q (f x))) :discharge [H3 c2]))
    (have d (<=> (Q (f x)) (Q (f y))) :by ((p/iff-intro (Q (f x)) (Q (f y))) a c))
    (have e (equal U (f x) (f y)) :discharge [Q d])
    (qed e)))
