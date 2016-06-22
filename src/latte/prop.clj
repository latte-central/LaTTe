(ns latte.prop
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.core :as latte :refer [defterm term type-of]])
  )


(def +examples-enabled+)

(defterm absurd
  "Absurdity."
  []
  (forall [α *] α))

(example
 (term absurd) => '(absurd))

(example
 (type-of absurd) => '✳)

;; (defthm ex-falso
;;   "Ex falso sequitur quolibet
;;    (proof by contradiction)."
;;   [[A :type]]
;;   (--> absurd A))

;; (proof ex-falso :term
;;   (lambda [x : absurd] (absurd A)))

(defterm neg
  "Logical negation."
  [[A :type]]
  (--> A absurd))


(example
 (term neg) => '(neg))

(example
 (type-of neg) => '(Π [A ✳] ✳))



