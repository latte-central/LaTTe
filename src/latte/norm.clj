(ns typetheory.beta
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [clojure.spec :as s])
  (:require [clojure.test.check :as tc])
  (:require [clojure.test.check.generators :as gen])
  (:require [clojure.test.check.properties :as prop])
  (:require [typetheory.syntax :as sx])
  )

;; (s/exercise ::sx/binder)

;;{
;; # Beta-reduction etc.
;;}

(def ^:private +examples-enabled+)

;;{
;; ## Beta-reduction

;; a tricky example :
;;  ((lambda [z :type] (lambda [x :type] (x y))) x)
;;   ~~> (lambda [x :type] (x x)    is wrong
;;
;;   ((lambda [z :type] (lambda [x :type] (x z))) x)
;; = ((lambda [z :type] (lambda [y :type] (y z))) x)
;;   ~~> (lambda [y :type] (y x)    is correct


(s/def ::redex (s/cat :rator (s/spec ::sx/bind)
                      :rand (s/spec ::sx/term)))



(example
 (s/valid? ::redex '((lambda [x :type] x) y)) => true)

(example
 (sx/validate ::redex '((lambda [x :type] (x x)) y))
 => '{:rator {:binder lambda,
              :binding [x [:type :type]],
              :body [:app {:rator [:var x],
                           :rand [:var x]}]},
      :rand [:var y]})

(defn beta-reduction [t]
  (sx/validate ::sx/term t)
  (if (s/valid? ::redex t)
    (let [x (first (second (first t)))
          body (nth (first t) 2)
          rand (second t)]
      (sx/subst body x rand))
    t))

(example
 (beta-reduction '((lambda [x :type] (x x)) y))
 => '(y y))

;;{
;; ## Normalization
;;}

(defn beta-norm- [t]
  (if (s/valid? ::redex t)
    [(beta-reduction t) true]
    (let [[tag _] (sx/validate ::sx/term t)]
      (case tag
        :bind (let [[binder [x ty] body] t]
                ;; 1) try reduction in binding type
                (let [[ty' red?] (beta-norm- ty)]
                  (if red?
                    [(list binder [x ty'] body) true]
                    ;; 2) try reduction in body
                    (let [[body' red?] (beta-norm- body)]
                      [(list binder [x ty] body') red?]))))
        :app (let [[left right] t
                   ;; 1) try left reduction
                   [left' red?] (beta-norm- left)]
               (if red?
                 [(list left' right) true]
                 ;; 2) try right reduction
                 (let [[right' red?] (beta-norm- right)]
                   [(list left right') red?])))

        [t false]))))

(defn beta-norm [t]
  (let [[t' _] (beta-norm- t)]
    t'))

(example
 (beta-norm '((lambda [x :type] x) y)) => 'y)

(example
 (beta-norm '(((lambda [x :type] x) y) z)) => '(y z))

(example
 (beta-norm '(lambda [y ((lambda [x :kind] x) :type)] y))
 => '(lambda [y :type] y))


(example
 (beta-norm '(z ((lambda [x :type] x) y))) => '(z y))

(example
 (beta-norm '(x y)) => '(x y))

(defn normalize [t]
  (let [[t' red?] (beta-norm- t)]
    (if red?
      (recur t')
      t')))

(example
 (normalize '(lambda [y ((lambda [x :kind] x) :type)] ((lambda [x :type] x) y)))
 => '(lambda [y :type] y))



(defn beta-eq? [t1 t2]
  (let [t1' (normalize t1)
        t2' (normalize t2)]
    (sx/alpha-eq? t1' t2')))

(example
 (beta-eq? '(lambda [z :type] z)
           '(lambda [y ((lambda [x :kind] x) :type)] ((lambda [x :type] x) y))) => true)

(def beta-eq-refl
  (prop/for-all
   [t (s/gen ::sx/term)]
   (beta-eq? t t)))

(example
 (:result (tc/quick-check 100 beta-eq-refl)) => true)




