(ns latte.prop
  (:require [latte.core :as latte :refer [defterm]])
  )


(defterm absurd
  "Absurdity."
  []
  (forall [α *] α))

(defterm neg
  "Logical negation."
  [[A :type]]
  (--> A absurd))
