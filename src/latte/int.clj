(ns latte.int
  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall proof]])

  (:require [latte.prop :as p :refer [and or not <=>]])
  
  (:require [latte.rel :as rel])

  (:require [latte.quant :as q :refer [exist]])

  (:require [latte.equal :as eq :refer [equal]])
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

(defthm exist-succ
  "An integer `y` is the successor of  *at least* another integer."
  [[y int]]
  (exist [x int] (equal int ((succ) x) y)))

(proof exist-succ :script
  (have a (forall [z int]
            (exist [x int] (equal int ((succ) x) z)))
        :by ((rel/bijective-is-surjective int int succ) (succ-bijective)))
  (qed ((a) y)))

(defthm single-succ-
  "An integer `y` is the successor *at most* another integer."
  [[y int]]
  (forall [x1 x2 int]
    (==> (equal int ((succ) x1) y)
         (equal int ((succ) x2) y)
         (equal int ((succ) x1) ((succ) x2)))))
;; there is a problem with:
;; (q/single int (lambda [x int] (equal int ((succ) x) y))))

(proof single-succ- :script
  (assume [x1 int
           x2 int
           u1 (equal int ((succ) x1) y)
           u2 (equal int ((succ) x2) y)]
    (have a (equal int y ((succ) x2)) :by ((eq/eq-sym int ((succ) x2) y) u2))
    (have b (equal int ((succ) x1) ((succ) x2))
          :by ((eq/eq-trans int ((succ) x1) y ((succ) x2))
               u1 (a)))
    (qed b)))


(defthm single-succ
  "An integer `y` is the successor *at most* another integer."
  [[y int]]
  (q/single int (lambda [x int] (equal int ((succ) x) y))))

(proof single-succ :script
  (assume [x1 int
           x2 int
           H1 (equal int ((succ) x1) y)
           H2 (equal int ((succ) x2) y)]
    (have a (equal int y ((succ) x2)) :by ((eq/eq-sym int ((succ) x2) y) H2))
    (have b (equal int ((succ) x1) ((succ) x2))
          :by ((eq/eq-trans int ((succ) x1) y ((succ) x2))
               H1 (a)))
    (have c (==> ((lambda [x int] (equal int ((succ) x) y)) x2)
                 (equal int ((succ) x1) ((succ) x2))) :discharge [H2 (b)])
    (have d (==> ((lambda [x int] (equal int ((succ) x) y)) x1)
                 ((lambda [x int] (equal int ((succ) x) y)) x2)
                 (equal int ((succ) x1) ((succ) x2))) :discharge [H1 (c)])
    (have e _ :discharge [x2 (d)])
    (have f _ ;(q/single int (lambda [x int] (equal int ((succ) x) y)))
          :discharge [x1 (e)]))
  (qed f))


(latte.kernel.norm/beta-delta-eq? {}
 (latte/term
  [y int]
  (forall [x1 x2 int]
    (==> (equal int ((succ) x1) y)
         (equal int ((succ) x2) y)
         (equal int ((succ) x1) ((succ) x2)))))
 (latte/term
  [y int]
  (q/single int (lambda [x int] (equal int ((succ) x) y)))))

(latte.kernel.norm/beta-delta-eq?
 {}
 (latte/term
  [y int]
  (forall [x1 x2 int]
    (==> (equal int ((succ) x1) y)
         (equal int ((succ) x2) y)
         (equal int ((succ) x1) ((succ) x2)))))
 (latte/term
  [y int]
  (forall [x1 x2 int]
    (==> ((lambda [x int] (equal int ((succ) x) y)) x1)
         ((lambda [x int] (equal int ((succ) x) y)) x2)
         (equal int ((succ) x1) ((succ) x2))))))

;; this is probably a bug ...
(latte.kernel.norm/beta-delta-eq?
 {}
 (latte/term
  [y int]
  (forall [x1 x2 int]
    (==> ((lambda [x int] (equal int ((succ) x) y)) x1)
         ((lambda [x int] (equal int ((succ) x) y)) x2)
         (equal int ((succ) x1) ((succ) x2)))))
 (latte/term
  [y int]
  (q/single int (lambda [x int] (equal int ((succ) x) y)))))


;; (definition single
;;   "The constraint that \"there exists at most\"..."
;;   [[T :type] [P (==> T :type)]]
;;   (forall [x y T]
;;     (==> (P x)
;;          (P y)
;;          (equal T x y))))


(defthm unique-succ
  "There is a unique successor to an integer `y`."
  [y int]
  (q/unique int (lambda [x int] (equal int ((succ) x) y)))) 
