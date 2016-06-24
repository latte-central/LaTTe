(ns latte.prop
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.core :as latte :refer [defterm term type-of defthm proof
                                          lambda forall]])
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
   (proof by contradiction, elimination for absurdity)."
  [[A :type]]
  (==> absurd A))

(proof ex-falso
       :term
       (lambda [f absurd] (f A)))

;; (proof ex-falso
;;        :script
;;        (assume [f absurd]
;;                (have A by (f A))))

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

;; (proof absurd-intro
;;        :script
;;        (assume [x A] [y (neg A)]
;;                (have absurd by (y x))))

(defterm land
  "logical conjunction."
  [[A :type] [B :type]]
  (prod [C :type] (==> (==> A B C)
                       C)))

(defthm land-intro
  "Introduction rule for logical conjunction."
  [[A :type] [B :type]]
  (==> A B
       (land A B)))

(proof land-intro
       :term
       (lambda [x A]
         (lambda [y B]
           (lambda [C :type]
             (lambda [z (==> A B C)]
               z x y)))))

;; (proof land-intro
;;        :script
;;        (assume [x A
;;                 y B
;;                 C :type
;;                 z (==> A B C)]
;;          (have [step1 (==> B C) :by (z x)
;;                 step2 C :by (z step1)
;;                 step3 (==> (==> A B C)
;;                         C) :discharge z step2]
;;            (qed (land A B) :discharge C step3)))))

