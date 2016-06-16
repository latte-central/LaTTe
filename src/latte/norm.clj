(ns latte.norm
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.syntax :as stx])
  )

;; (s/exercise ::sx/binder)

;;{
;; # Normalization
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

(defn redex? [t]
  (and (stx/app? t)
       (stx/lambda? (first t))))

(example
 (redex? '[(lambda [x :type] x) y]) => true)

(defn beta-reduction [t]
  (if (redex? t)
    (let [[[_ [x _] body] rand] t]
      (stx/subst body x rand))
    (throw (ex-info "Cannot beta-reduce. Not a redex" {:term t}))))

(example
 (beta-reduction '[(lambda [x :type] [x x]) y])
 => '[y y])

(defn beta-step [t]
  (cond
    ;; reduction of a redex
    (redex? t) [(beta-reduction t) true]
    ;; binder
    (stx/binder? t)
    (let [[binder [x ty] body] t]
      ;; 1) try reduction in binding type
      (let [[ty' red?] (beta-step ty)]
        (if red?
          [(list binder [x ty'] body) true]
          ;; 2) try reduction in body
          (let [[body' red?] (beta-step body)]
            [(list binder [x ty] body') red?]))))
    ;; application
    (stx/app? t)
    (let [[left right] t
          ;; 1) try left reduction
          [left' red?] (beta-step left)]
      (if red?
        [[left' right] true]
        ;; 2) try right reduction
        (let [[right' red?] (beta-step right)]
          [[left right'] red?])))
    ;; reference
    (stx/ref? t)
    (let [[def-name & args] t
          [args' red?] (reduce (fn [[res red?] arg]
                                 (let [[arg' red?'] (beta-step arg)]
                                   [(conj res arg') (or red? red?')])) [[] false] args)]
      [(list* def-name args') red?])
    ;; other cases
    :else [t false]))

(defn beta-red [t]
  (let [[t' _] (beta-step t)]
    t'))

(example
 (beta-red '[(lambda [x :type] x) y]) => 'y)

(example
 (beta-red '[[(lambda [x :type] x) y] z]) => '[y z])

(example
 (beta-red '(lambda [y [(lambda [x :kind] x) :type]] y))
 => '(lambda [y :type] y))


(example
 (beta-red '[z [(lambda [x :type] x) y]]) => '[z y])

(example
 (beta-red '[x y]) => '[x y])

;;{
;; ## Delta-reduction (unfolding of definitions)
;;}

(defn delta-reduction [def-env t]
  (if (not (stx/ref? t))
    (throw (ex-info "Cannot delta-reduce: not a reference term." {:term t}))
    (let [[name & args] t]
      (if (not (get def-env name))
        (throw (ex-info "No such definition" {:term t :def-name name}))
        (let [sdef (get def-env name)]
          (if (not= (count args) (:arity sdef))
            (throw (ex-info "Wrong arity for definition." {:term t :def-name name :expected-arity (:arity sdef)}))
            (if (:parsed-term sdef)
              [(stx/subst (:parsed-term sdef) (zipmap (map first (:params sdef)) args)) true]
              [t false])))))))

(example
 (delta-reduction '{test {:arity 3
                          :params [[x :type] [y :kind] [z :type]]
                          :parsed-term [y (lambda [t :type] [x [z t]])]}}
                  '(test [a b] c [t (lambda [t] t)]))
 => '[[c (lambda [t' :type] [[a b] [[t (lambda [t] t)] t']])] true])

(example
 (delta-reduction '{test {:arity 3
                          :params [[x :type] [y :kind] [z :type]]}}
                  '(test [a b] c [t (lambda [t] t)]))
 => '[(test [a b] c [t (lambda [t] t)]) false])


(defn delta-step [def-env t]
  (cond
    ;; reduction of a delta-redex
    (stx/ref? t) (delta-reduction def-env t)
    ;; binder
    (stx/binder? t)
    (let [[binder [x ty] body] t]
      ;; 1) try reduction in binding type
      (let [[ty' red?] (delta-step def-env ty)]
        (if red?
          [(list binder [x ty'] body) true]
          ;; 2) try reduction in body
          (let [[body' red?] (delta-step def-env body)]
            [(list binder [x ty] body') red?]))))
    ;; application
    (stx/app? t)
    (let [[left right] t
          ;; 1) try left reduction
          [left' red?] (delta-step def-env left)]
      (if red?
        [[left' right] true]
        ;; 2) try right reduction
        (let [[right' red?] (delta-step def-env right)]
          [[left right'] red?])))
    ;; reference
    (stx/ref? t)
    (let [[def-name & args] t
          [args' red?] (reduce (fn [[res red?] arg]
                                 (let [[arg' red?'] (delta-step def-env arg)]
                                   [(conj res arg') (or red? red?')])) [[] false] args)]
      [(list* def-name args') red?])
    ;; other cases
    :else [t false]))

(example
 (delta-step {} 'x) => '[x false])

(example
 (delta-step '{test {:arity 1
                     :params [[x :type]]
                     :parsed-term [x x]}}
             '[y (test [t t])])
 => '[[y [[t t] [t t]]] true])

;;{
;; ## Normalization (up-to beta/delta)
;;}


(defn normalize
  ([t] (normalize {} t))
  ([def-env t]
   (let [[t' red?] (beta-step t)]
     (if red?
       (recur def-env t')
       (let [[t'' red?] (delta-step def-env t)]
         (if red?
           (recur def-env t'')
           t''))))))

(example
 (normalize '(lambda [y [(lambda [x :kind] x) :type]] [(lambda [x :type] x) y]))
 => '(lambda [y :type] y))


(defn beta-eq? [t1 t2]
  (let [t1' (normalize t1)
        t2' (normalize t2)]
    (stx/alpha-eq? t1' t2')))

(example
 (beta-eq? '(lambda [z :type] z)
           '(lambda [y [(lambda [x :kind] x) :type]] [(lambda [x :type] x) y])) => true)



