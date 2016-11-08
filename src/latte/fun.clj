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
            :by (Hg x y <b>)))
    (qed <c>)))

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
        (have <b> (equal T x1 x2) :by (Hf x1 x2 <a>))))
    (qed <b>)))

(defthm bijective-unique
  "A bijective function has exactly one antecedent for each image."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective T U f)
       (forall [y U] (q/unique T (lambda [x T] (equal U (f x) y))))))

(proof bijective-unique
    :script
  (assume [Hf (bijective T U f)]
    (have <a> (injective T U f)
          :by ((bijective-is-injective T U f) Hf))
    (have <b> (surjective T U f)
          :by ((bijective-is-surjective T U f) Hf))
    (assume [y U]
      (have <c> (q/ex T (lambda [x T] (equal U (f x) y)))
            :by (<b> y))
      (have <d> (q/single T (lambda [x T] (equal U (f x) y)))
            :by ((injective-single T U f)
                 <a> y))
      (have <e> (q/unique T (lambda [x T] (equal U (f x) y)))
            :by (p/and-intro% <c> <d>))
      (qed <e>))))

(definition inverse
  "The inverse of function `f`."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (lambda [y U]
    (q/the T (lambda [x T] (equal U (f x) y))
           ((bijective-unique T U f) b y))))

(defthm inverse-prop
  "The basic property of the inverse function."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (forall [y U] (equal U (f ((inverse T U f b) y)) y)))

(proof inverse-prop
    :script
  (assume [y U]
    (have <a> (equal U (f ((inverse T U f b) y)) y)
          :by (q/the-prop T
                          (lambda [z T] (equal U (f z) y))
                          (((bijective-unique T U f) b) y)))
    (qed <a>)))

(defthm inverse-prop-conv
  "The basic property of the inverse function,
 the converse of [[inverse-prop]]."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (forall [x T] (equal T ((inverse T U f b) (f x)) x)))

(proof inverse-prop-conv
    :script
  (assume [x T]
    (have <a> (equal U (f ((inverse T U f b) (f x))) (f x))
          :by ((inverse-prop T U f b) (f x)))
    (have <b> (equal T ((inverse T U f b) (f x)) x)
          :by (((bijective-is-injective T U f) b)
               ((inverse T U f b) (f x)) x
               <a>))
    (qed <b>)))

(defthm inverse-surjective
  "The inverse function of a bijection, is surjective."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (surjective U T (inverse T U f b)))

(proof inverse-surjective
    :script
  (have <a> (injective T U f) :by ((bijective-is-injective T U f) b))
  (have inv-f (==> U T) :by (inverse T U f b))
  (assume [x T]
    (have y U :by (f x))
    (have <b> (equal U (f (inv-f y)) (f x))
          :by ((inverse-prop T U f b) (f x)))
    (have <c> (equal T (inv-f y) x) :by (<a> (inv-f y) x <b>))
    (have <d> (exists [y U] (equal T (inv-f y) x))
          :by ((q/ex-intro U (lambda [z U] (equal T (inv-f z) x)) y)
               <c>))
    (qed <d>)))


(defthm inverse-injective
  "The inverse function of a bijection, is injective."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (injective U T (inverse T U f b)))

(proof inverse-injective
    :script
  (have inv-f (==> U T) :by (inverse T U f b))
  (assume [x U
           y U
           Hxy (equal T (inv-f x) (inv-f y))]
    (have <a> (equal U (f (inv-f x)) (f (inv-f y)))
          :by ((eq/eq-cong T U f (inv-f x) (inv-f y)) Hxy))
    (have <b> (equal U x (f (inv-f x)))
          :by ((eq/eq-sym U (f (inv-f x)) x)
               ((inverse-prop T U f b) x)))
    (have <c> (equal U (f (inv-f y)) y)
          :by ((inverse-prop T U f b) y))
    (have <d> (equal U x (f (inv-f y)))
          :by ((eq/eq-trans U x (f (inv-f x)) (f (inv-f y)))
               <b> <a>))
    (have <e> (equal U x y)
          :by ((eq/eq-trans U x (f (inv-f y)) y)
               <d> <c>)))
  (qed <e>))

(defthm inverse-bijective
  "The inverse of a bijection is a bijection."
  [[T :type] [U :type] [f (==> T U)] [b (bijective T U f)]]
  (bijective U T (inverse T U f b)))

(proof inverse-bijective
    :script
  (have <a> _ :by (p/and-intro% (inverse-injective T U f b)
                                (inverse-surjective T U f b)))
  (qed <a>))


