(ns latte.int
  "A formalization of the type of integers."
  
  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall proof assume have]])

  (:require [latte.prop :as p :refer [and or not <=>]])
  
  (:require [latte.rel :as rel])

  (:require [latte.quant :as q :refer [exist]])

  (:require [latte.equal :as eq :refer [equal]])

  (:require [latte.subset :as set :refer [elem]])
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

(defaxiom succ-bijective
  "The successor function is bijective."
  []
  (rel/bijective int int succ))

(defthm succ-surjective
  "The successor function is surjective."
  []
  (rel/surjective int int succ))

(proof succ-surjective :term
  ((rel/bijective-is-surjective int int succ) succ-bijective))

(defthm succ-injective
  "The successor function is injective."
  []
  (rel/injective int int succ))

(proof succ-injective :term
  ((rel/bijective-is-injective int int succ) succ-bijective))

(defthm exist-succ
  "An integer `y` is the successor of  *at least* another integer."
  [[y int]]
  (exist [x int] (equal int (succ x) y)))

(proof exist-succ :term
  (succ-surjective y))

(defthm single-succ
  "An integer `y` is the successor of *at most* another integer."
  [[y int]]
  (q/single int (lambda [x int] (equal int (succ x) y))))

(proof single-succ :script
  (assume [x1 int
           x2 int
           H1 (equal int (succ x1) y)
           H2 (equal int (succ x2) y)]
    (have a (equal int y (succ x2)) :by ((eq/eq-sym int (succ x2) y) H2))
    (have b (equal int (succ x1) (succ x2))
          :by ((eq/eq-trans int (succ x1) y (succ x2))
               H1 a))
    (have c (equal int x1 x2) :by (succ-injective x1 x2 b))
    (qed c)))

(defthm unique-succ
  "There is a unique successor to an integer `y`."
  [[y int]]
  (q/unique int (lambda [x int] (equal int (succ x) y))))

(proof unique-succ :term
  ((p/and-intro (q/ex int (lambda [x int] (equal int (succ x) y)))
     (q/single int (lambda [x int] (equal int (succ x) y))))
   (exist-succ y)
   (single-succ y)))

(definition pred
  "The predecessor of `y`."
  [[y int]]
  (q/the int
         (lambda [x int] (equal int (succ x) y)) 
         (unique-succ y)))

(defthm succ-of-pred
  "The succesor of the predecessor of `y` is ... `y`."
  [[y int]]
  (equal int (succ (pred y)) y))

(proof succ-of-pred :term
  (q/the-prop int (lambda [x int] (equal int (succ x) y)) (unique-succ y)))

(defthm pred-of-succ
  "The predecessor of the successor of `y` is ... `y`."
  [[y int]]
  (equal int (pred (succ y)) y))

(proof pred-of-succ :script
  (have a (equal int (succ (pred (succ y))) (succ y))
        :by (succ-of-pred (succ y)))
  (have b (equal int (pred (succ y)) y)
        :by (succ-injective (pred (succ y)) y a))
  (qed b))

(defaxiom int-induct
  "The induction principle for integers
(as an axiom)."
  [[P (==> int :type)]]
  (==> (and (P zero)
            (forall [x int] (==> (P x)
                                 (and (P (succ x))
                                      (P (pred x))))))
       (forall [x int] (P x))))

(definition nat-succ-prop
  "A property verified by all successors of natural integers."
  [[P (==> int :type)]]
  (forall [y int] (==> (P y) (P (succ y)))))

(definition nat
  "The subset of natural integers."
  []
  (lambda [x int]
    (forall [P (==> int :type)]
      (==> (and (P zero)
                (nat-succ-prop P))
           (P x)))))

(defthm nat-zero
  "Zero is a natural integer."
  []
  (elem int zero nat))

(proof nat-zero :script
  (assume [P (==> int :type)
           H (and (P zero)
                  (nat-succ-prop P))]
    (have a (P zero) :by ((p/and-elim-left (P zero)
                                           (nat-succ-prop P))
                          H))
    (qed a)))

(defthm nat-succ
  "The successor of a natural integer is a natural integer."
  [[x int]]
  (==> (elem int x nat)
       (elem int (succ x) nat)))

(proof nat-succ :script
  (assume [H (elem int x nat)]
    (assume [Q (==> int :type)
             H2 (and (Q zero)
                     (nat-succ-prop Q))]
      (have a (==> (and (Q zero)
                        (nat-succ-prop Q))
                   (Q x)) :by (H Q))
      (have b (Q x) :by (a H2))
      (have c (==> (Q x) (Q (succ x)))
            :by ((p/and-elim-right (Q zero) (nat-succ-prop Q))
                 H2 x))
      (have d (Q (succ x)) :by (c b))
      (qed d))))

(defaxiom nat-zero-has-no-pred
  "An important axiom of the natural integer subset
wrt. [[pred]]."
  []
  (not (elem int (pred zero) nat)))

(defthm nat-zero-is-not-succ
  "Zero is not a successor of a natural integer.

This is the first Peano 'axiom' (here theorem, based
 on integers) for natural integers."
  []
  (forall [x int]
    (==> (elem int x nat)
         (not (equal int (succ x) zero)))))

(proof nat-zero-is-not-succ :script
  (assume [x int
           H (elem int x nat)]
    (assume [H2 (equal int (succ x) zero)]
      (have a (equal int (pred (succ x)) (pred zero))
            :by ((eq/eq-cong int int pred (succ x) zero) H2))
      (have b (equal int x (pred (succ x)))
            :by ((eq/eq-sym int (pred (succ x)) x)
                 (pred-of-succ x)))
      (have c (equal int x (pred zero))
            :by ((eq/eq-trans int x (pred (succ x)) (pred zero))
                 b a))
      (have d (elem int (pred zero) nat)
            :by ((eq/eq-subst int nat x (pred zero))
                 c H))
      (have e p/absurd :by (nat-zero-has-no-pred d))
      (qed e))))

(defthm nat-succ-injective
  "Successor is injective, the second Peano 'axiom'
here a simple consequence of [[succ-injective]]."
  []
  (forall [x y int]
    (==> (elem int x nat)
         (elem int y nat)
         (equal int (succ x) (succ y))
         (equal int x y))))

(proof nat-succ-injective :script
  (assume [x int
           y int
           H1 (elem int x nat)
           H2 (elem int y nat)
           H3 (equal int (succ x) (succ y))]
    (have a (equal int x y)
          :by (succ-injective x y H3))
    ;; TODO: multiple discharge at once ?
    ;; Alternative: put unused assumptions in
    ;; term
    (have b _ :discharge [H3 a])
    (have c _ :discharge [H2 b])
    (have d _ :discharge [H1 c])
    (qed d)))

(defthm nat-induct
  "The induction principle for natural integers.
This is the third Peano axiom but it can be
derived from [[int-induct]]."
  [[P (==> int :type)]]
  (==> (and (P zero)
            (forall [x int]
              (==> (elem int x nat)
                   (P x)
                   (P (succ x)))))
       (forall [x int]
         (==> (elem int x nat)
              (P x)))))

(proof nat-induct :script
  (have Q _ :by (lambda [z int]
                  (and (elem int z nat)
                       (P z))))
  (assume [u (and (P zero)
                  (forall [x int]
                    (==> (elem int x nat)
                         (P x)
                         (P (succ x)))))]
    (have a (P zero) :by ((p/and-elim-left
                           (P zero)
                           (forall [x int]
                             (==> (elem int x nat)
                                  (P x)
                                  (P (succ x)))))
                          u))
    (have b (forall [x int]
              (==> (elem int x nat)
                   (P x)
                   (P (succ x))))
          :by ((p/and-elim-right
                (P zero)
                (forall [x int]
                  (==> (elem int x nat)
                       (P x)
                       (P (succ x)))))
               u))
    (have c (Q zero) :by ((p/and-intro (elem int zero nat)
                                       (P zero))
                          nat-zero a))
    (assume [y int
             v (Q y)]
      (have d (elem int y nat)
            :by ((p/and-elim-left (elem int y nat)
                                  (P y)) v))
      (have e (P y)
            :by ((p/and-elim-right (elem int y nat)
                                   (P y)) v))
      (have f (elem int (succ y) nat)
            :by ((nat-succ y) d))
      (have g (==> (P y) (P (succ y)))
            :by (b y d))
      (have h (P (succ y)) :by (g e))
      (have i (Q (succ y)) :by ((p/and-intro (elem int (succ y) nat)
                                             (P (succ y)))
                                f h))
      (have j (==> (Q y) (Q (succ y))) :discharge [v i])
      (have k (nat-succ-prop Q) :discharge [y j]))
    (have l (and (Q zero)
                 (nat-succ-prop Q)) :by ((p/and-intro (Q zero)
                                                      (nat-succ-prop Q)) c k))
    
    (assume [x int
             w (elem int x nat)]
      (have m (Q x) :by (w Q l))
      (have n (P x) :by ((p/and-elim-right (elem int x nat)
                                           (P x)) m))
      (have o (==> (elem int x nat)
                   (P x)) :discharge [w n])
      (have p (forall [x int]
                (==> (elem int x nat)
                     (P x))) :discharge [x o])
      (qed p))))
      

;; (defaxiom int-recur
;;   "The recursion principle for integers.

;; According to [TT&FP,p. 318], this is derivable,
;;  but we introduce it as an axiom since the
;; derivation seems rather complex."
;;   [[T :type] [x T] [f-succ (==> T T)] [f-pred (==> T T)]]
;;   (q/unique (==> int T)
;;             (lambda [g (==> int T)]
;;               (and (equal T (g 0) x)
;;                    (forall [y int]
;;                      (and (==> 
