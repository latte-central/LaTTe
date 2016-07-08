(ns latte.equal
  "The formal definition of equality, and its basic properties."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [defterm defthm forall assume have proof]])

  (:require [latte.prop :as p :refer [<=> and or not]])
  )

(defterm equal
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
    (qed (a))))

(defthm eq-sym
  "The symmetry property of equality."
  [[T :type] [x T] [y T]]
  (==> (equal T x y)
       (equal T y x)))

(proof eq-sym :script
  (assume [Heq (equal T x y)
           P (==> T :type)]
    (have a (<=> (P x) (P y)) :by (Heq P))
    (have b (<=> (P y) (P x)) :by ((p/iff-sym (P x) (P y)) (a)))
    (have c _ :discharge [P (b)])
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
          :by ((p/iff-trans (P x) (P y) (P z)) (a) (b)))
    (have d _ :discharge [P (c)])
    (qed d)))



            
