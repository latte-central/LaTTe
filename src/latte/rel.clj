(ns latte.rel
  "A **relation** between elements of
a given type `T`, is formalized with type `(==> T T :type)`.

The type `(==> T U :type)` for arbitrary types `T` and `U` gives
  the relations between elements of `T` and elements of `U`.

With an extra property, this is also the type of **functional
 relations**, given by the type `(==> T U)`.

This namespace provides some important properties about such
  relations."

  (:require [latte.core :as latte :refer [definition defaxiom defthm
                                          forall]])

  (:require [latte.prop :as p :refer [and or not]])

  (:require [latte.equal :as eq :refer [equal]])

  (:require [latte.quant :as q :refer [exist]])
  
  )

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

(definition injective
  "An injective function."
  [[T :type] [U :type] [F (==> T U)]]
  (forall [x y T]
    (==> (equal U (F x) (F y))
         (equal T x y))))

(definition surjective
  "A surjective function."
  [[T :type] [U :type] [F (==> T U)]]
  (forall [y U] (exist [x T] (equal U (F x) y))))

(definition bijective
  "A bijective function."
  [[T :type] [U :type] [F (==> T U)]]
  (and (injective T U F)
       (surjective T U F)))

