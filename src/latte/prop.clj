(ns latte.prop
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.core :as latte :refer [defterm term type-of defthm proof]])
  )


(def +examples-enabled+)

(defterm absurd
  "Absurdity."
  []
  (forall [α *] α))

(example
 (type-of absurd) => '✳)

(defthm ex-falso
  "Ex falso sequitur quodlibet
   (proof by contradiction)."
  [[A :type]]
  (==> absurd A))

(proof ex-falso
       :term
       (lambda [f absurd] (f A)))

(defterm neg
  "Logical negation."
  [[A :type]]
  (==> A absurd))

(example
 (type-of neg) => '(Π [A ✳] ✳))

(defthm absurd-intro
  "Introduction rule for absurdity."
  [[A :type]]
  (==> A (neg A)
       absurd))

(proof absurd-intro
       :term
       (lambda [x A]
               (lambda [y (neg A)]
                       (y x))))

