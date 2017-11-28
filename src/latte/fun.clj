(ns latte.fun
  "A **function** with domain `T` and codomain `U` 
  has type `(==> T U)`.

   This namespace provides some important properties about such
  functions."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defaxiom defthm defimplicit
                                          proof assume have pose qed]]
            [latte.prop :as p :refer [and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]))

(definition injective-def
  "An injective function."
  [[T :type] [U :type] [f (==> T U)]]
  (forall [x y T]
    (==> (equal (f x) (f y))
         (equal x y))))

(defimplicit injective
  "The function `f` is injective, cf. [[injective-def]]."
  [def-env ctx [f f-type]]
  (let [[T U] (p/decompose-impl-type def-env ctx f-type)]
    (list #'injective-def T U f)))

(definition surjective-def
  "A surjective function."
  [[T :type] [U :type] [f (==> T U)]]
  (forall [y U] (exists [x T] (equal (f x) y))))

(defimplicit surjective
  "The function `f` is surjective, cf. [[surjective-def]]."
  [def-env ctx [f f-type]]
  (let [[T U] (p/decompose-impl-type def-env ctx f-type)]
    (list #'surjective-def T U f)))

(definition bijective-def
  "A bijective function."
  [[T :type] [U :type] [f (==> T U)]]
  (and (injective f)
       (surjective f)))

(defimplicit bijective
  "The function `f` is bijective, cf. [[bijective-def]]."
  [def-env ctx [f f-type]]
  (let [[T U] (p/decompose-impl-type def-env ctx f-type)]
    (list #'bijective-def T U f)))

(defthm bijective-is-surjective
  "A bijection is a surjection."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective f)
       (surjective f)))

(proof 'bijective-is-surjective
  (assume [H (bijective f)]
    (have <a> (surjective f) :by (p/and-elim-right H)))
  (qed <a>))

(defthm bijective-is-injective
  "A bijection is an injection."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective f)
       (injective f)))

(proof 'bijective-is-injective
  (assume [H (bijective f)]
    (have <a> (injective f) :by (p/and-elim-left H)))
  (qed <a>))

(definition compose-def
  "The composition of two functions."
  [[T :type] [U :type] [V :type]
   [f (==> U V)] [g [==> T U]]]
  (lambda [x T] (f (g x))))

(defimplicit compose
  "The composition of `f` and `g`, cf. [[compose-def]]."
  [def-env ctx [f f-type] [g g-type]]
  (let [[U V] (p/decompose-impl-type def-env ctx f-type)
        [T _] (p/decompose-impl-type def-env ctx g-type)]
    (list #'compose-def T U V f g)))

(defthm compose-injective
  "The composition of two injective functions is injective."
  [[T :type] [U :type] [V :type]
   [f (==> U V)] [g [==> T U]]]
  (==> (injective f)
       (injective g)
       (injective (compose f g))))

(proof 'compose-injective  
  (assume [Hf (injective f)
           Hg (injective g)]
    (assume [x T
             y T
             Hinj (equal ((compose f g) x)
                         ((compose f g) y))]
      (have <a> (equal (f (g x)) (f (g y))) :by Hinj)
      (have <b> (equal (g x) (g y))
            :by (Hf (g x) (g y) <a>))
      (have <c> (equal x y)
            :by (Hg x y <b>))))
  (qed <c>))

(defthm injective-single
  "An injective function has at most one antecedent for each image."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (injective f)
       (forall [y U] (q/single (lambda [x T] (equal (f x) y))))))

(proof 'injective-single   
  (assume [Hf (injective f)]
    (assume [y U]
      (assume [x1 T
               x2 T
               Hx1 (equal (f x1) y)
               Hx2 (equal (f x2) y)]
        (have <a1> (equal y (f x2)) :by (eq/eq-sym Hx2))
        (have  <a> (equal (f x1) (f x2))
               :by (eq/eq-trans Hx1 <a1>))
        (have <b> (equal x1 x2) :by (Hf x1 x2 <a>)))))
  (qed <b>))

(defthm bijective-unique
  "A bijective function has exactly one antecedent for each image."
  [[T :type] [U :type] [f (==> T U)]]
  (==> (bijective f)
       (forall [y U] (q/unique (lambda [x T] (equal (f x) y))))))

(proof 'bijective-unique  
  (assume [Hf (bijective f)]
    (have <a> (injective f)
          :by ((bijective-is-injective T U f) Hf))
    ;; [:print-def '<a> {}]
    (have <b> (surjective f)
          :by ((bijective-is-surjective T U f) Hf))
    ;;[:print-def '<b> {}]
    (assume [y U]
      (have <c> (q/ex (lambda [x T] (equal (f x) y)))
            :by (<b> y))
      [:print-def '<c> {}]
      (have <d> (q/single (lambda [x T] (equal (f x) y)))
            :by ((injective-single T U f) <a> y))
      [:print-def '<d> {}]
      (have <e> (q/unique (lambda [x T] (equal (f x) y)))
            :by (p/and-intro <c> <d>))))
  (qed <e>))

(definition inverse-def
  "The inverse of bijective function `f`."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (lambda [y U]
    (q/the (lambda [x T] (equal (f x) y))
           ((bijective-unique T U f) b y))))

(defimplicit inverse
  "The inverse of bijective function `f`, cf. [[inverse-def]]."
  [def-env ctx [f f-type] [b b-type]]
  (let [[T U] (p/decompose-impl-type def-env ctx f-type)]
    (list #'inverse-def T U f b)))

(defthm inverse-prop
  "The basic property of the inverse of a bijective function `f`."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (forall [y U] (equal (f ((inverse f b) y)) y)))

(proof 'inverse-prop  
  (assume [y U]
    (have <a> (equal (f ((inverse f b) y)) y)
          :by (q/the-prop (lambda [z T] (equal (f z) y))
                          (((bijective-unique T U f) b) y))))
  (qed <a>))

(defthm inverse-prop-conv
  "The basic property of the inverse function,
 the converse of [[inverse-prop]]."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (forall [x T] (equal ((inverse f b) (f x)) x)))

(proof 'inverse-prop-conv  
  (assume [x T]
    (have <a> (equal (f ((inverse f b) (f x))) (f x))
          :by ((inverse-prop T U f b) (f x)))
    (have <b> (equal ((inverse f b) (f x)) x)
          :by (((bijective-is-injective T U f) b)
               ((inverse f b) (f x)) x
               <a>)))
  (qed <b>))

(defthm inverse-surjective
  "The inverse function of a bijection, is surjective."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (surjective (inverse f b)))

(proof 'inverse-surjective 
  (have <a> (injective f) :by ((bijective-is-injective T U f) b))
  (pose inv-f := (inverse f b))
  (assume [x T]
    (pose y := (f x))
    (have <b> (equal (f (inv-f y)) (f x))
          :by ((inverse-prop T U f b) (f x)))
    (have <c> (equal (inv-f y) x) :by (<a> (inv-f y) x <b>))
    (have <d> (exists [y U] (equal (inv-f y) x))
          :by ((q/ex-intro (lambda [z U] (equal (inv-f z) x)) y)
               <c>)))
  (qed <d>))


(defthm inverse-injective
  "The inverse function of a bijection, is injective."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (injective (inverse f b)))

(proof 'inverse-injective 
  (pose inv-f := (inverse f b))
  (assume [x U
           y U
           Hxy (equal (inv-f x) (inv-f y))]
    (have <a> (equal (f (inv-f x)) (f (inv-f y)))
          :by (eq/eq-cong f Hxy))
    (have <b> (equal (f (inv-f x)) x)
          :by ((inverse-prop T U f b) x))
    (have <c> (equal x (f (inv-f x)))
          :by (eq/eq-sym <b>))
    (have <d> (equal (f (inv-f y)) y)
          :by ((inverse-prop T U f b) y))
    (have <e> (equal x (f (inv-f y)))
          :by (eq/eq-trans <c> <a>))
    (have <f> (equal x y)
          :by (eq/eq-trans <e> <d>)))
  (qed <f>))

(defthm inverse-bijective
  "The inverse of a bijection is a bijection."
  [[T :type] [U :type] [f (==> T U)] [b (bijective f)]]
  (bijective (inverse f b)))

(proof 'inverse-bijective
  (have <a> _ :by (p/and-intro (inverse-injective T U f b)
                               (inverse-surjective T U f b)))
  (qed <a>))

