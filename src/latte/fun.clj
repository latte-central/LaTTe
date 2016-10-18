(ns latte.fun
  "A **function** with domain `T` and codomain `U` 
  has type `(==> T U)`.

   This namespace provides some important properties about such
  functions."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defaxiom defthm
                                          forall lambda ==>
                                          proof assume have]]
            [latte.prop :as p :refer [and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]))

(definition injective
  "An injective function."
  [[T :type] [U :type] [f (==> T U)]]
  (forall [x y T]
    (==> (equal U (f x) (f y))
         (equal T x y))))

(definition surjective
  "A surjective function."
  [[T :type] [U :type] [f (==> T U)]]
  (forall [y U] (exists [x T] (equal U (f x) y))))

(definition bijective
  "A bijective function."
  [[T :type] [U :type] [f (==> T U)]]
  (and (injective T U f)
       (surjective T U f)))

(defthm bijective-is-surjective
  "A bijection is a surjection."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective T U f)
       (surjective T U f)))

(proof bijective-is-surjective :script
  (assume [H (bijective T U f)]
    (have a (surjective T U f) :by (p/and-elim-right% H))
    (qed a)))

(defthm bijective-is-injective
  "A bijection is an injection."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective T U f)
       (injective T U f)))

(proof bijective-is-injective :script
  (assume [H (bijective T U f)]
    (have a (injective T U f) :by (p/and-elim-left% H))
    (qed a)))


(definition compose
  "The composition of two functions."
  [[T :type] [U :type] [V :type]
   [f (==> U V)] [g [==> T U]]]
  (lambda [x T] (f (g x))))

(defthm compose-injective
  "The composition of two injective functions is injective."
  [[T :type] [U :type] [V :type]
   [f (==> U V)] [g [==> T U]]]
  (==> (injective U V f)
       (injective T U g)
       (injective T V (compose T U V f g))))

(proof compose-injective
    :script
  (assume [Hf (injective U V f)
           Hg (injective T U g)]
    (assume [x T
             y T
             Hinj (equal V
                         ((compose T U V f g) x)
                         ((compose T U V f g) y))]
      (have <a> (equal V (f (g x)) (f (g y))) :by Hinj)
      (have <b> (equal U (g x) (g y))
            :by (Hf (g x) (g y) <a>))
      (have <c> (equal T x y)
            :by (Hg x y <b>))
      (have <d> (injective T V (compose T U V f g))
            :discharge [x y Hinj <c>]))
    (qed <d>)))

(defthm injective-single
  "An injective function has at most one antecedent for each image."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (injective T U f)
       (forall [y U] (q/single T (lambda [x T] (equal U (f x) y))))))

(proof injective-single
    :script
  (assume [Hf (injective T U f)]
    (assume [y U]
      (assume [x1 T
               x2 T
               Hx1 (equal U (f x1) y)
               Hx2 (equal U (f x2) y)]
        (have  <a> (equal U (f x1) (f x2))
               :by ((eq/eq-trans U (f x1) y (f x2))
                    Hx1
                    ((eq/eq-sym U (f x2) y) Hx2)))
        (have <b> (equal T x1 x2) :by (Hf x1 x2 <a>))
        (have <c> (q/single T (lambda [x T] (equal U (f x) y)))
              :discharge [x1 x2 Hx1 Hx2 <b>]))
      (have <d> _ :discharge [y <c>]))
    (qed <d>)))




