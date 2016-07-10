(ns latte.subset
  "Set-theoretic notions based on the subset
  approach of type theory.

  The main idea is to consider a typed variant of
  a mathematical set as a predicate over a given type.

  In LaTTe what is called a **set** will be technically-speaking
  a subset of a type, hence a predicate over a given type.

  The main drawback of the approach is that sets
  are not considered as types (hence type inhabitation
  and set elemthood are distinct notions).

  The advantage is that it is quite a workable approach in
  practice,
  and that it does not require any extension to the kernel
  such as sigma-types."

    (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [defterm defthm forall assume have proof lambda]])

  (:require [latte.prop :as p :refer [<=> and or not]])

  (:require [latte.equal :as eq :refer [equal]])
  )

(defterm set
  "The set (or subset of a type) constructor."
  [[T :type]]
  (==> T :type))

(defterm elem
  "Set membership."
  [[T :type] [x T] [s (set T)]]
  (s x))

(defterm subseteq
  "Subset or equal relation."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (forall [x T]
    (==> (elem T x s1)
         (elem T x s2))))

(defterm seteq
  "Equality on sets."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (and (subseteq T s1 s2)
       (subseteq T s2 s1)))

(defterm union
  "Set union."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (or (elem T x s1)
        (elem T x s2))))

(defthm union-commute
  "Set union commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq T
         (union T s1 s2)
         (union T s2 s1)))  

(proof union-commute :script
  (assume [x T
           H (elem T x (union T s1 s2))]
    (have a1 (or (elem T x s1)
                 (elem T x s2)) :by H)
    (have a2 _ :by (p/or-sym (elem T x s1) (elem T x s2)))
    (have a3 (or (elem T x s2)
                (elem T x s1)) :by ((a2) (a1)))
    (have a4 (elem T x (union T s2 s1)) :by (a3))
    (have a5 (==> (elem T x (union T s1 s2))
                  (elem T x (union T s2 s1))) :discharge [H (a4)])
    (have a (subseteq T
                      (union T s1 s2)
                      (union T s2 s1)) :discharge [x (a5)]))
  (assume [x T
           H (elem T x (union T s2 s1))]
    (have b1 (elem T x (union T s1 s2))
          :by ((p/or-sym (elem T x s2) (elem T x s1)) H))
    (have b2 (==> (elem T x (union T s2 s1))
                  (elem T x (union T s1 s2))) :discharge [H (b1)])
    (have b (subseteq T
                      (union T s2 s1)
                      (union T s1 s2)) :discharge [x (b2)]))
  (have c (seteq T
                 (union T s1 s2)
                 (union T s2 s1))
        :by ((p/and-intro (subseteq T (union T s1 s2) (union T s2 s1))
                          (subseteq T (union T s2 s1) (union T s1 s2)))
             (a) (b)))
  (qed c))
         

(defterm intersection
  "Set intersection."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (forall [x T]
    (and (elem T x s1)
         (elem T x s2))))

