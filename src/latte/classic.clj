(ns latte.classic

  "The axioms of classical logic, and basic derived
  proof rules."

  (:refer-clojure :exclude [and or not])

  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.core :as latte :refer [defterm term type-of defthm defaxiom
                                          lambda forall assume proof try-proof]])

  (:require [latte.prop :as p :refer [or not and]])
  )


(defaxiom excluded-middle
  "The law of excluded middle for classical logic.

This axiom can be assumed for classical
(sometimes called \"non-constructive\") reasoning."
  [[A :type]]
  (or A (not A)))



