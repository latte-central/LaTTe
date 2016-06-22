(ns latte.simple-types
  (:require [clojure.test :as test :refer [deftest is]])
  (:require [latte.core :as l :refer [=== type-of term check-type?]])
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
  (is (=== (type-of [sigma :type]
                    (lambda [x sigma] x))
           (term [sigma :type] (==> sigma sigma))))

  (is (check-type? [sigma :type]
                   (lambda [x sigma] x)
                   (==> sigma sigma)))
  
  (is (=== (type-of [sigma :type]
                    [tau :type]
                    [y (--> sigma tau)]
                    [x sigma]
                    (y x))
          'tau))

  (is (=== (type-of [alpha :type] [beta :type] [gamma :type]
                    [x (--> alpha alpha)]
                    [y (--> (--> alpha alpha) beta)]
                    (lambda [u gamma] (y x)))
           (term [beta :type] [gamma :type]
                 (--> gamma beta))))
  )







