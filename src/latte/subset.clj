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

  The advantage is that it is quite an effective approach in
  practice,
  and that it does not require any extension to the kernel
  such as dependent pairs and sigma-types."

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm forall assume have proof lambda]])

  (:require [latte.prop :as p :refer [<=> and or not]])

  (:require [latte.equal :as eq :refer [equal]])
  )

(definition set
  "The set (or subset of a type) constructor."
  [[T :type]]
  (==> T :type))

(definition elem
  "Set membership."
  [[T :type] [x T] [s (set T)]]
  (s x))

(definition subseteq
  "Subset or equal relation."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (forall [x T]
    (==> (elem T x s1)
         (elem T x s2))))

(defthm subseteq-refl
  "The subset relation is reflexive."
  [[T :type] [s (set T)]]
  (subseteq T s s))

(proof subseteq-refl :script
  (assume [x T
           H (elem T x s)]
    (have a (elem T x s) :by H)
    (have b (==> (elem T x s)
                 (elem T x s)) :discharge [H a])
    (have c (subseteq T s s) :discharge [x b])
    (qed c)))

(defthm subseteq-trans
  "The subset relation is transitive."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (subseteq T s1 s2)
       (subseteq T s2 s3)
       (subseteq T s1 s3)))

(proof subseteq-trans :script
  (assume [H1 (subseteq T s1 s2)
           H2 (subseteq T s2 s3)]
    (assume [x T]
      (have a (==> (elem T x s1)
                   (elem T x s2)) :by (H1 x))
      (have b (==> (elem T x s2)
                   (elem T x s3)) :by (H2 x))
      (have c (==> (elem T x s1)
                   (elem T x s3)) :by ((p/impl-trans (elem T x s1)
                                                     (elem T x s2)
                                                     (elem T x s3)) a b))
      (have d (subseteq T s1 s3) :discharge [x c]))
    (qed d)))

(definition seteq
  "Equality on sets."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (and (subseteq T s1 s2)
       (subseteq T s2 s1)))

(defthm seteq-refl
  "Set equality is reflexive."
  [[T :type] [s (set T)]]
  (seteq T s s))

(proof seteq-refl :script
  (have a (subseteq T s s) :by (subseteq-refl T s))
  (have b (and (subseteq T s s)
               (subseteq T s s))
        :by ((p/and-intro (subseteq T s s)
                          (subseteq T s s)) a a))
  (qed b))

(defthm seteq-sym
  "Set equality is symmetric."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (seteq T s1 s2)
       (seteq T s2 s1)))

(proof seteq-sym :script
  (assume [H (seteq T s1 s2)]
    (have a (subseteq T s1 s2) :by ((p/and-elim-left (subseteq T s1 s2)
                                                       (subseteq T s2 s1)) H))
    (have b (subseteq T s2 s1) :by ((p/and-elim-right (subseteq T s1 s2)
                                                        (subseteq T s2 s1)) H))
    (have c (seteq T s2 s1) :by ((p/and-intro (subseteq T s2 s1)
                                              (subseteq T s1 s2)) b a))
    (qed c)))

(defthm seteq-trans
  "Set equality is transitive."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (seteq T s1 s2)
       (seteq T s2 s3)
       (seteq T s1 s3)))

(proof seteq-trans :script
  (assume [H1 (seteq T s1 s2)
           H2 (seteq T s2 s3)]
    (have a1 (subseteq T s1 s2) :by ((p/and-elim-left (subseteq T s1 s2)
                                                      (subseteq T s2 s1)) H1))
    (have b1 (subseteq T s2 s3) :by ((p/and-elim-left (subseteq T s2 s3)
                                                      (subseteq T s3 s2)) H2))
    (have c1 (subseteq T s1 s3) :by ((subseteq-trans T s1 s2 s3) a1 b1))
    (have a2 (subseteq T s2 s1) :by ((p/and-elim-right (subseteq T s1 s2)
                                                       (subseteq T s2 s1)) H1))
    (have b2 (subseteq T s3 s2) :by ((p/and-elim-right (subseteq T s2 s3)
                                                       (subseteq T s3 s2)) H2))
    (have c2 (subseteq T s3 s1) :by ((subseteq-trans T s3 s2 s1) b2 a2))
    (have d (seteq T s1 s3) :by ((p/and-intro (subseteq T s1 s3)
                                              (subseteq T s3 s1)) c1 c2))
    (qed d)))


(definition union
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
                (elem T x s1)) :by (a2 a1))
    (have a4 (elem T x (union T s2 s1)) :by a3)
    (have a5 (==> (elem T x (union T s1 s2))
                  (elem T x (union T s2 s1))) :discharge [H a4])
    (have a (subseteq T
                      (union T s1 s2)
                      (union T s2 s1)) :discharge [x a5]))
  (assume [x T
           H (elem T x (union T s2 s1))]
    (have b1 (elem T x (union T s1 s2))
          :by ((p/or-sym (elem T x s2) (elem T x s1)) H))
    (have b2 (==> (elem T x (union T s2 s1))
                  (elem T x (union T s1 s2))) :discharge [H b1])
    (have b (subseteq T
                      (union T s2 s1)
                      (union T s1 s2)) :discharge [x b2]))
  (have c (seteq T
                 (union T s1 s2)
                 (union T s2 s1))
        :by ((p/and-intro (subseteq T (union T s1 s2) (union T s2 s1))
                          (subseteq T (union T s2 s1) (union T s1 s2)))
             a b))
  (qed c))

(definition intersection
  "Set intersection."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem T x s1)
         (elem T x s2))))

(defthm intersection-elim-left
  "Elimination rule for intersection (left operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem T x (intersection T s1 s2))
       (elem T x s1)))

(proof intersection-elim-left :script
  (assume [H (elem T x (intersection T s1 s2))]
    (have a (elem T x s1) :by ((p/and-elim-left (elem T x s1)
                                                (elem T x s2)) H))
    (qed a)))

(defthm intersection-elim-right
  "Elimination rule for intersection (right operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem T x (intersection T s1 s2))
       (elem T x s2)))

(proof intersection-elim-right :script
  (assume [H (elem T x (intersection T s1 s2))]
    (have a (elem T x s2) :by ((p/and-elim-right (elem T x s1)
                                                 (elem T x s2)) H))
    (qed a)))

(defthm intersection-commute
  "Set intersection commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq T
         (intersection T s1 s2)
         (intersection T s2 s1)))  

(proof intersection-commute :script
  (assume [x T
           H (elem T x (intersection T s1 s2))]
    (have a1 (elem T x (intersection T s2 s1))
          :by ((p/and-sym (elem T x s1) (elem T x s2)) H))
    (have a2 (==> (elem T x (intersection T s1 s2))
                  (elem T x (intersection T s2 s1))) :discharge [H a1])
    (have a (subseteq T
                      (intersection T s1 s2)
                      (intersection T s2 s1)) :discharge [x a2]))
  (assume [x T
           H (elem T x (intersection T s2 s1))]
    (have b1 (elem T x (intersection T s1 s2))
          :by ((p/and-sym (elem T x s2) (elem T x s1)) H))
    (have b2 (==> (elem T x (intersection T s2 s1))
                  (elem T x (intersection T s1 s2))) :discharge [H b1])
    (have b (subseteq T
                      (intersection T s2 s1)
                      (intersection T s1 s2)) :discharge [x b2]))
  (have c (seteq T
                 (intersection T s1 s2)
                 (intersection T s2 s1))
        :by ((p/and-intro (subseteq T (intersection T s1 s2) (intersection T s2 s1))
                          (subseteq T (intersection T s2 s1) (intersection T s1 s2)))
             a b))
  (qed c))


(definition fullset
  "The full set of a type
(all the inhabitants of the type are element
of the full set)."
  [[T :type]]
  (lambda [x T] p/truth))

(defthm fullset-intro
  "Introduction rule for the full set."
  [[T :type]]
  (forall [x T]
    (elem T x (fullset T))))

(proof fullset-intro :script
  (assume [x T]
    (have a (elem T x (fullset T)) :by p/truth-is-true)
    (have b _ :discharge [x a])
    (qed b)))

(definition emptyset
  "The empty set of a type."
  [[T :type]]
  (lambda [x T] p/absurd))

(defthm emptyset-prop
  "The main property of the empty set."
  [[T :type]]
  (forall [x T]
    (not (elem T x (emptyset T)))))

(proof emptyset-prop :script
  (assume [x T
           H (elem T x (emptyset T))]
    (have a p/absurd :by H)
    (have b (not (elem T x (emptyset T))) :discharge [H a])
    (have c _ :discharge [x b])
    (qed c)))
