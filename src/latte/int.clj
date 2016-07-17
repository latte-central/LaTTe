(ns latte.int
  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall]])


  )


(defaxiom int
  "The type of integers."
  []
  :type)

(defaxiom zero
  "The integer zero."
  []
  int)

(defaxiom succ
  "The successor integer."
  []
  (==> int int))


