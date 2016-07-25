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
    (have c (rel/injective int int succ)
                                        ;(forall [x y int]
                                        ;  (==> (equal int ((succ) x) ((succ y)))
                                        ;       (equal int x y)))
          :by ((rel/bijective-is-injective int int succ) (succ-bijective)))
    (have d (equal int x1 x2) :by ((c) x1 x2 (b)))
    (qed d)))

(defthm unique-succ
  "There is a unique successor to an integer `y`."
  [[y int]]
  (q/unique int (lambda [x int] (equal int ((succ) x) y))))

(proof unique-succ :script
  (qed ((p/and-intro (q/ex int (lambda [x int] (equal int ((succ) x) y)))
                     (q/single int (lambda [x int] (equal int ((succ) x) y))))
        (exist-succ y)
        (single-succ y))))

