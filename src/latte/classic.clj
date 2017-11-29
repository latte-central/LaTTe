(ns latte.classic

  "The axioms of classical logic, and basic derived
  proof rules.

By convention, all the imports from this namespace must
be done in a qualified way, i.e. favor `classic/not-not-impl`
 instead of the unqualifed `not-not-impl`."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [defthm defaxiom proof
                                          assume have qed]]
            [latte.utils :as u]
            [latte.prop :as p :refer [or not and <=>]]))


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


;; for the following proof disjunction must be made
;; transparent

(u/set-opacity! #'or false)

(proof 'not-not-impl 
  (assume [H (not (not A))]
    (have <em> (or A (not A)) :by (excluded-middle-ax A))
    (have <a> (==> (==> A A)
                   (==> (not A) A)
                   A) :by (<em> A))
    (have <b> (==> A A) :by (p/impl-refl A))
    (have <c> (==> (==> (not A) A)
                   A) :by (<a> <b>))
    (assume [z (not A)]
            (have <d> p/absurd :by (H z))
            (have <e> (==> p/absurd A) :by (p/ex-falso A))
            (have <f> A :by (<e> <d>)))
    (have <g> A :by (<c> <f>)))
  (qed <g>))

(u/set-opacity! #'or true)


(defthm not-not
  "The double-negation law of classical logic."
  [[A :type]]
  (<=> A (not (not A))))

(proof 'not-not
  (have <a> (==> A (not (not A))) :by (p/impl-not-not A))
  (have <b> (==> (not (not A)) A) :by (not-not-impl A))
  (have <c> _ :by (p/and-intro <a> <b>))
  (qed <c>))

(defthm not-impl-or-intro
  "An alternative elimination rule for disjunction.

Remark: this introduction is only provable in
classical logic."
  [[A :type] [B :type]]
  (==> (==> (not A) B)
       (or A B)))

(proof 'not-impl-or-intro
  (assume [H (==> (not A) B)]
    (assume [Hnot (not (or A B))]
      (assume [x A]
        (have <a1> _ :by (p/or-intro-left-thm A B))
        (have <a2> (or A B) :by (<a1> x))
        (have <a> p/absurd :by (Hnot <a2>)))
      (assume [y B]
        (have <b1> _ :by (p/or-intro-right-thm A B))
        (have <b2> (or A B) :by (<b1> y))
        (have <b> p/absurd :by (Hnot <b2>)))
      (have <c> B :by (H <a>))
      (have <d> p/absurd :by (<b> <c>)))
    (have <e> (or A B) :by ((not-not-impl (or A B)) <d>)))
  (qed <e>))

