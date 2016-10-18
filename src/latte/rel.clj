(ns latte.rel
  "A **relation** (or endo-relation) between elements of
a given type `T`, is formalized with type `(==> T T :type)`.

  This namespace provides some important properties about such
  relations."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defaxiom defthm
                                          forall lambda ==>
                                          proof assume have]]
            [latte.prop :as p :refer [and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]))

(definition rel
  "The type of relations."
  [[T :type]]
  (==> T T :type))

(definition reflexive
  "A reflexive relation."
  [[T :type] [R (rel T)]]
  (forall [x T] (R x x)))

(definition symmetric
  "A symmetric relation."
  [[T :type] [R (rel T)]]
  (forall [x y T]
    (==> (R x y)
         (R y x))))

(definition transitive
  "A transitive relation."
  [[T :type] [R (rel T)]]
  (forall [x y z T]
    (==> (R x y)
         (R y z)
         (R x z))))

(definition equivalence
  "An equivalence relation."
  [[T :type] [R (rel T)]]
  (and (reflexive T R)
       (and (symmetric T R)
            (transitive T R))))

