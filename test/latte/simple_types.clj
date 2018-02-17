(ns latte.simple-types
  (:require [clojure.test :as test :refer [deftest is]])
  (:require [latte.core :as l :refer [term lambda type-of type-check?]])
  (:require [latte-kernel.norm :as n :refer [beta-eq?]])
  )

;;{
;;  # Simple types
;;
;; Simply typed lambda calculus is denoted as: λ⟶
;;
;; The tests here are for simple types and mostly taken from the book:
;;
;; > Type Theory and Formal Proofs - an Introduction
;; > (Chapter 2: Simply typed lambda calculus)
;; > by R. Nederpelt and H. Geuvers
;;
;;}

(deftest basic-terms
  ;; Examples 2.2.6
  ;; (1) When x has type σ, then the identity function λx . x has type σ → σ
  (let [;; (Π [x sigma] sigma)
        type-of-result (type-of [sigma :type] (lambda [x sigma] x))
        ;; (Π [⇧ sigma] sigma)
        term-result    (term [sigma :type] (==> sigma sigma))]
    (is (and (beta-eq? type-of-result term-result)
             ;; "normal" non-equality from clojure.core
             (not= type-of-result term-result))))

  (is (true? (type-check? [sigma :type] (lambda [x sigma] x)
                          (==> sigma sigma))))

  (let [type-of-result (type-of [sigma :type]
                                [tau :type]
                                [y (==> sigma tau)]
                                [x sigma]
                                (y x))
        term-result 'tau]
    (is (and (is (beta-eq? type-of-result term-result))
             ;; "normal" equality from clojure.core
             (is (=        type-of-result term-result)))))

  (let [;; (Π [u gamma] beta)
        type-of-result (type-of [alpha :type] [beta :type] [gamma :type]
                                [x (==> alpha alpha)]
                                [y (==> (==> alpha alpha) beta)]
                                (lambda [u gamma] (y x)))
        ;; (Π [⇧ gamma] beta)
        term-result    (term [beta :type] [gamma :type] (==> gamma beta))]
    (is (and (beta-eq? type-of-result term-result)
             ;; "normal" non-equality from clojure.core
             (not=     type-of-result term-result))))
  )
