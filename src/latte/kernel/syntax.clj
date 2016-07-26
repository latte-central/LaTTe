
(ns latte.kernel.syntax
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [clojure.set :as set])
  )

;;{
;; # The syntax of type theory
;;}

(def ^:private +examples-enabled+)

;;{
;; ## Lambda terms
;;}

(defn kind? [t]
  (= t '□))

(defn type? [t]
  (= t '✳))

(defn sort? [t]
  (or (kind? t)
      (type? t)))

(defn variable? [t]
  (symbol? t))

(defn binder? [t]
  (and (list? t)
       (contains? '#{λ Π} (first t))))

(defn lambda? [t]
  (and (seq? t)
       (= (first t) 'λ)))

(defn prod? [t]
  (and (seq? t)
       (= (first t) 'Π)))

(defn app? [t]
  (and (vector? t)
       (= (count t) 2)))

(defn ref? [t]
  (and (seq? t)
       (not (contains? '#{λ Π} (first t)))))

;;{
;; ## Free and bound variables
;;}

(defn free-vars [t]
  (cond
    (variable? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (set/union (free-vars ty)
                             (disj (free-vars body) x)))
    (app? t) (set/union (free-vars (first t))
                        (free-vars (second t)))
    (ref? t) (apply set/union (map free-vars (rest t)))
    :else #{}))

(example
 (free-vars 'x) => #{'x})

(example
 (free-vars '[x y]) => #{'x 'y})

(example
 (free-vars '(λ [x t] [x [y z]])) => #{'t 'y 'z})

(example
 (free-vars '(Π [x t] [x [y z]])) => #{'t 'y 'z})

(example
 (free-vars '(λ [x t] (test x y z))) => '#{t y z})

(defn vars [t]
  (cond
    (variable? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (set/union (vars ty) (vars body)))
    (app? t) (set/union (vars (first t))
                                (vars (second t)))
    (ref? t) (apply set/union (map vars (rest t)))
    :else #{}))

(example
 (vars 'x) => #{'x})

(example
 (vars '[x y]) => #{'x 'y})

(example
 (vars '(λ [x t] (test x [y z]))) => #{'t 'x 'y 'z})

(example
 (vars '(Π [x t] (test x [y z]))) => #{'t 'x 'y 'z})

(defn bound-vars [t]
  (set/difference (vars t) (free-vars t)))

(example
 (bound-vars 'x) => #{})

(example
 (bound-vars '[x y]) => #{})

(example
 (bound-vars '(λ [x t] (test x [y z]))) => #{'x})

(example
 (bound-vars '(λ [x t] (test t [y z]))) => #{})

(example
 (bound-vars '(Π [x t] (test x [y z]))) => #{'x})

;;{
;; ## Substitution
;;}

(defn mk-fresh
  ([base forbid] (mk-fresh base 0 forbid))
  ([base level forbid]
   (let [suffix (case level
                  0 ""
                  1 "'"
                  2 "''"
                  3 "'''"
                  (str "-" level))
         candidate (symbol (str base suffix))]
     (if (contains? forbid candidate)
       (recur base (inc level) forbid)
       candidate))))

(example
 (mk-fresh 'x '#{x x' x''}) => 'x''')

(example
 (mk-fresh 'x '#{x x' x'' x'''}) => 'x-4)

(defn subst- [t sub forbid]
  (cond
    ;; variables
    (variable? t) [(get sub t t) (conj forbid t)]
    ;; binders (λ, Π)
    (binder? t)
    (let [[binder [x ty] body] t
          [x' sub' forbid']
          (if (contains? forbid x)
            (let [x' (mk-fresh x forbid)]
              [x' (assoc sub x x') (conj forbid x')])
            [x (dissoc sub x) forbid])
          [ty' forbid''] (subst- ty sub forbid')
          [body' forbid'''] (subst- body sub' forbid'')]
      ;; (println "term=" (list binder [x' ty'] body') "sub=" sub')
      [(list binder [x' ty'] body')
       forbid'''])
    ;; applications
    (app? t)
    (let [[rator forbid'] (subst- (first t) sub forbid)
          [rand forbid''] (subst- (second t) sub forbid')]
      [[rator rand] forbid''])
    ;; references
    (ref? t) (let [[args forbid']
                   (reduce (fn [[ts forbid] t]
                             (let [[t' forbid'] (subst- t sub forbid)]
                               [(conj ts t') forbid'])) ['() forbid] (rest t))]
               [(conj (into '() args) (first t)) forbid'])
    ;; other cases
    :else [t forbid]))

(defn subst
  ([t x u] (subst t {x u}))
  ([t sub]
   (let [forbid (set/union
                 (apply set/union (map vars (vals sub)))
                 (into #{} (keys sub))
                 (free-vars t))
         [t' _] (subst- t sub forbid)]
     t')))

(example
 (subst 'x {'x '✳}) => '✳)

(example
 (subst 'y {'x '✳}) => 'y)

(example
 (subst '[y x] {'x '✳}) => '[y ✳])

(example
 (subst '[x (λ [x ✳] (test x y z y))] {'x '✳, 'y '□})
 => '[✳ (λ [x' ✳] (test x' □ z □))])

(example
 (subst '[x (Π [x ✳] [y x])] {'x '✳, 'y 'x})
 => '[✳ (Π [x' ✳] [x x'])])
;; and not: '(:type (Π [x :type] (x x)))


;;{
;; ## Alpha-equivalence
;;}

(defn alpha-norm- [t sub level]
  (cond
    ;; variables
    (variable? t) [(get sub t t) level]
    ;; binders (λ, Π)
    (binder? t)
    (let [[binder [x ty] body] t
          x' (symbol (str "_" level))
          [ty' level'] (alpha-norm- ty sub (inc level))
          [body' level''] (alpha-norm- body (assoc sub x x') level')]
      [(list binder [x' ty'] body')
       level''])
    ;; applications
    (app? t)
    (let [[left' level'] (alpha-norm- (first t) sub level)
          [right' level''] (alpha-norm- (second t) sub level')]
      [[left' right'] level''])
    ;; references
    (ref? t) (let [[args level']
                   (reduce (fn [[args level] arg]
                             (let [[arg' level'] (alpha-norm- arg sub level)]
                               [(conj args arg') level'])) ['() level] (rest t))]
               [(conj (into '() args) (first t)) level'])
    ;; other cases
    :else [t level]))

(defn alpha-norm [t]
  (let [[t' _] (alpha-norm- t {} 1)]
    t'))

(example
 (alpha-norm 'x) => 'x)

(example
 (alpha-norm '(λ [x ✳] x))
 => '(λ [_1 ✳] _1))

(example
 (alpha-norm '[x (λ [x ✳] (test x y [x z]))])
 => '[x (λ [_1 ✳] (test _1 y [_1 z]))])

(defn alpha-eq? [t1 t2]
  (= (alpha-norm t1)
     (alpha-norm t2)))

(example
 (alpha-eq? '(λ [x ✳] x)
            '(λ [y ✳] y)) => true)

