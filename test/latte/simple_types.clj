(ns latte.simple-types
  (:require [clojure.test :as test :refer [deftest is]])
  (:require [latte.presyntax :as s])
  (:require [latte.typing :as t])
  (:require [latte.norm :as n])
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
  (is (n/beta-eq?
       (t/type-of '[[sigma :type]]
                  (s/parse '(lambda [x sigma] x)))
       (s/parse '(--> sigma sigma))))

  (is (n/beta-eq?
       (t/type-of [['sigma :type] ['tau :type]
                   ['y (s/parse '(--> sigma tau))] '[x sigma]]
                  (s/parse '(y x)))
       'tau))

  (is (n/beta-eq?
       (t/type-of [['alpha :type] ['beta :type] ['gamma :type]
                    ['x (s/parse '(--> alpha alpha))]
                    ['y (s/parse '(--> (--> alpha alpha) beta))]]
                  (s/parse '(lambda [u gamma] (y x))))
       (s/parse '(--> gamma beta))))
  )







