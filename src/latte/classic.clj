(ns latte.classic

  "The axioms of classical logic, and basic derived
  proof rules.

By convention, all the imports from this namespace must
be done in a qualified way, i.e. favor `classic/not-not-impl`
 instead of the unqualifed `not-not-impl`."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [defthm defaxiom proof]])

  (:require [latte.prop :as p :refer [or not and <=>]])
  )


(defaxiom excluded-middle-ax
  "The law of excluded middle for classical logic.

This axiom can be assumed for classical
(sometimes called \"non-constructive\") reasoning."
  [[A :type]]
  (or A (not A)))

(defthm not-not-impl
  "The double-negation law of classical logic,
 obtained from the axiom of the excluded middle
(the only-if part of double negation).

This can be seen as an elimination rule for ¬¬ (not-not) propositions."
  [[A :type]]
  (==> (not (not A)) A))

(proof not-not-impl
       :script
       (assume [H (not (not A))]
         (have (em) (or A (not A)) :by (excluded-middle-ax A))
         (have (a) (==> (==> A A)
                        (==> (not A) A)
                        A) :by ((em) A))
         (have (b) (==> A A) :by (p/impl-refl A))
         (have (c) (==> (==> (not A) A)
                        A) :by ((a) (b)))
         (assume [z (not A)]
           (have (d) p/absurd :by (H z))
           (have (e) (==> p/absurd A) :by (p/ex-falso A))
           (have (f) A :by ((e) (d)))
           (have (g) (==> (not A) A) :discharge [z (f)]))
         (have (h) A :by ((c) (g)))
         (qed (h))))

(defthm not-not
  "The double-negation law of classical logic."
  [[A :type]]
  (<=> A (not (not A))))

(proof not-not :script
  (have (a) (==> A (not (not A))) :by (p/impl-not-not A))
  (have (b) (==> (not (not A)) A) :by (not-not-impl A))
  (have (c) _ :by (p/and-intro (==> A (not (not A)))
                               (==> (not (not A)) A)))
  (qed ((c) (a) (b))))

(defthm not-impl-or-intro
  "An alternative elimination rule for disjunction.

Remark: this introduction is only provable in
classical logic."
  [[A :type] [B :type]]
  (==> (==> (not A) B)
       (or A B)))

(proof not-impl-or-intro :script
  (assume [H (==> (not A) B)]
    (assume [Hnot (not (or A B))]
      (assume [x A]
        (have (a1) _ :by (p/or-intro-left A B))
        (have (a2) (or A B) :by ((a1) x))
        (have (a3) p/absurd :by (Hnot (a2)))
        (have (a) (not A) :discharge [x (a3)]))
      (assume [y B]
        (have (b1) _ :by (p/or-intro-right A B))
        (have (b2) (or A B) :by ((b1) y))
        (have (b3) p/absurd :by (Hnot (b2)))
        (have (b) (not B) :discharge [y (b3)]))
      (have (c) B :by (H (a)))
      (have (d) p/absurd :by ((b) (c)))
      (have (e) (not (not (or A B))) :discharge [Hnot (d)]))
    (have (f) (or A B) :by ((not-not-impl (or A B)) e))
    (qed (f))))



