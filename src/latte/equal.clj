(ns latte.equal
  "The formal definition of equality, and its basic properties."

  (:refer-clojure :exclude [and or not])

  (:require
   [latte.kernel.syntax :as stx]
   [latte.kernel.norm :as norm]
   [latte.kernel.typing :as ty]
   [latte.core :as latte :refer [definition defthm defspecial
                                          forall lambda ==>
                                          assume have proof]]
   [latte.prop :as p :refer [<=> and or not]]))

(definition equal
  "The intuitionistic, second-order definition of equality.
This corresponds to Leibniz's *indiscernibility of identicals*."
  [[T :type] [x T] [y T]]
  (forall [P (==> T :type)]
    (<=> (P x) (P y))))

(defn decompose-equal-type [def-env ctx t]
  (if (clojure.core/and (seq t)
                        (= (count t) 4)
                        (= (first t) #'latte.equal/equal))
    [:ok (second t) (nth t 2) (nth t 3)]
    (let [[t ok?] (latte.kernel.norm/delta-step def-env t)]
      (if ok?
        (recur def-env ctx t)
        ;; XXX: cannot decompose further becayse
        ;; we cannot retrieve the x and y of the
        ;; definition ... needs a form of unification.
        [:ko nil nil nil]))))

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
    (qed b)))

(defspecial eq-sym%
  "Symmetry of equality, a special version of [[eq-sym]]."
  [def-env ctx eq-term]
  (let [[status ty] (ty/type-of-term def-env ctx eq-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-sym%
                                           :term eq-term
                                           :from ty}))
      (do
        (let [[status T x y] (decompose-equal-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-sym%
                                                             :term eq-term
                                                             :type ty}))
            [(list #'eq-sym T x y) eq-term]))))))

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
    (qed c)))

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
      (have a (Q (f y)) :by (a1 H1 H2)))
    (have b (equal T y x) :by ((eq-sym T x y) H1))
    (assume [H3 (Q (f y))]
      (have c1 _ :by (eq-subst T (lambda [z T] (Q (f z))) y x))
      (have c (Q (f x)) :by (c1 b H3)))
    (have d (<=> (Q (f x)) (Q (f y))) :by ((p/iff-intro (Q (f x)) (Q (f y))) a c))
    (qed d)))


