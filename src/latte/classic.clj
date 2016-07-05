(ns latte.classic

  "The axioms of classical logic, and basic derived
  proof rules."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [defterm term type-of defthm defaxiom
                                          lambda forall assume proof try-proof]])

  (:require [latte.prop :as p :refer [or not and]])
  )


(defaxiom excluded-middle-ax
  "The law of excluded middle for classical logic.

This axiom can be assumed for classical
(sometimes called \"non-constructive\") reasoning."
  [[A :type]]
  (or A (not A)))

(defthm double-negation-thm
  "The double-negation law of classical logic,
 obtained from the axiom of the excluded middle."
  [[A :type]]
  (==> (not (not A)) A))

(proof double-negation-thm
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



