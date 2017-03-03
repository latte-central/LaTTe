(ns latte.simple-types
  (:require [clojure.test :as test :refer [deftest is]])
  (:require [latte.core :as l :refer [==> term lambda type-of type-check?]])
  (:require [latte.kernel.norm :as n :refer [beta-eq?]])
  )

;;{
;;  # Simple types
;;
;; The tests in this file are for simple types,
;; and mostly taken from the book:
;;
;; > Type Theory and Formal Proofs - an Introduction
;; > (Chapter 2: Simply typed lambda calculus)
;; > by R. Nederpelt and H. Geuvers
;;
;;}

(deftest basic-terms
  ;; Examples 2.2.6
  ;; (1) When x has type σ, then the identity function λx . x has type σ → σ
  (is (beta-eq? (type-of [sigma :type] (lambda [x sigma] x)) ; (Π [x sigma] sigma)
                (term [sigma :type] (==> sigma sigma))       ; (Π [⇧ sigma] sigma)
                ))

  (is (type-check? [sigma :type] (lambda [x sigma] x)
                   (==> sigma sigma)))

  (is (beta-eq? (type-of [sigma :type]
                         [tau :type]
                         [y (==> sigma tau)]
                         [x sigma]
                         (y x))      ; tau
                'tau                 ; tau
                ))

  (is (beta-eq? (type-of [alpha :type] [beta :type] [gamma :type]
                         [x (==> alpha alpha)]
                         [y (==> (==> alpha alpha) beta)]
                         (lambda [u gamma] (y x)))   ; (Π [u gamma] beta)
                   (term [beta :type] [gamma :type]
                         (==> gamma beta))           ; (Π [⇧ gamma] beta)
                   ))
  )
