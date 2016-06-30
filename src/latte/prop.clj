(ns latte.prop
  (:refer-clojure :exclude [and or not])
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.core :as latte :refer [defterm term type-of defthm
                                          lambda forall assume proof]])
  )


(def +examples-enabled+)


(defthm impl-refl
  "Implication is reflexive."
  [[A :type]]
  (==> A A))

;; (proof impl-refl
;;        :term
;;        (lambda [x A] x))

(proof impl-refl
       :script
       (assume [x A]
         (have concl A :by x)
         (qed concl)))

(defthm impl-trans
  "Implication is transitive."
  [[A :type] [B :type] [C :type]]
  (==> (==> A B)
       (==> B C)
       (==> A C)))

(proof impl-trans
       :script
       (assume [H1 (==> A B)
                H2 (==> B C)
                x A]
         (have step1 B :by (H1 x))
         (have step2 C :by (H2 (step1)))
         (have step3 (==> A C) :discharge [x step2])
         (qed step3)))

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

;; (proof ex-falso
;;        :term
;;        (lambda [f absurd] (f A)))

(proof ex-falso
       :script
       (assume [f absurd]
         (qed (f A))))

(defterm not
  "Logical negation."
  [[A :type]]
  (==> A absurd))

(example
 (type-of not) => '(Π [A ✳] ✳))

(defthm absurd-intro
  "Introduction rule for absurdity."
  [[A :type]]
  (==> A (not A)
       absurd))

;; (proof absurd-intro
;;        :term
;;        (lambda [x A]
;;          (lambda [y (neg A)]
;;            (y x))))

(proof absurd-intro
       :script
       (assume [x A
                y (not A)]
         (have concl absurd :by (y x))
         (qed concl)))

(defthm impl-not-not
  "The if half of double negation."
  [[A :type]]
  (==> A (not (not A))))

;; (neg (neg A))
;; = (==> (neg A) absurd)
;; = (==> (==> A absurd) absurd) 

(proof impl-not-not
       :script
       (assume [x A
                H (not A)]
         (have step1 absurd :by (H x))
         (have step2 (not (not A)) :discharge [H step1])
         (qed step2)))

(defterm and
  "logical conjunction."
  [[A :type] [B :type]]
  (forall [C :type]
    (==> (==> A B C)
      C)))

(defthm and-intro
  "Introduction rule for logical conjunction."
  [[A :type] [B :type]]
  (==> A B
       (and A B)))

;; (proof land-intro
;;        :term
;;        (lambda [x A]
;;          (lambda [y B]
;;            (lambda [C :type]
;;              (lambda [z (==> A B C)]
;;                z x y)))))

(proof and-intro
       :script
       (assume [x A
                y B
                C :type
                z (==> A B C)]
         (have step1 (==> B C) :by (z x))
         (have step2 C :by ((step1) y))
         (have step3 (==> (==> A B C)
                          C) :discharge [z step2])
         (have concl (land A B) :discharge [C step3])
         (qed concl)))

(defthm and-elim-left
  "Elimination rule for logical conjunction.
   This one only keeps the left-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       A))

(proof and-elim-left
       :script
       (assume [H1 (and A B)
                x A
                y B]
         (have <a> (==> (==> A B A) A) :by (H1 A))
         (assume [H2 (==> A B A)]
           (have <b> (==> B A) :by (H2 x))
           (have <c> A :by ((<b>) y))
           (have <d> (==> (==> A B A) A) :discharge [H2 <c>])
           (showdef <d>))))



