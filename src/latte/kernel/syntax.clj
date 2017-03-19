
(ns latte.kernel.syntax
  (:require [clj-by.example :refer [example do-for-example]]
            [clojure.set :as set]
            [latte.kernel.lnsyntax :as ln]))


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

(defn subst- [t sub forbid rebind]
  (let [[t' forbid']
        (cond
          ;; variables
          (variable? t) (if-let [x (get rebind t)]
                          [x (conj forbid t)]
                          [(get sub t t) (conj forbid t)])
          ;; binders (λ, Π)
          (binder? t)
          (let [[binder [x ty] body] t
                [x' rebind' forbid']
                (if (contains? forbid x)
                  (let [x' (mk-fresh x forbid)]
                    [x' (assoc rebind x x') (conj forbid x')])
                  [x rebind (conj forbid x)])
                [ty' forbid''] (subst- ty sub forbid' rebind)
                [body' forbid'''] (subst- body sub forbid'' rebind')]
            ;; (println "term=" (list binder [x' ty'] body') "sub=" sub')
            [(list binder [x' ty'] body')
             forbid'''])
          ;; applications
          (app? t)
          (let [[rator forbid'] (subst- (first t) sub forbid rebind)
                [rand forbid''] (subst- (second t) sub forbid' rebind)]
            [[rator rand] forbid''])
          ;; references
          (ref? t) (let [[args forbid']
                         (reduce (fn [[ts forbid] t]
                                   (let [[t' forbid'] (subst- t sub forbid rebind)]
                                     [(conj ts t') forbid'])) ['() forbid] (rest t))]
                     [(conj (into '() args) (first t)) forbid'])
          ;; other cases
          :else [t forbid])]
    ;;(println "[subst-] t=" t "sub=" sub "forbid=" forbid "rebind=" rebind)
    ;;(println "   ==> " t')
    [t' forbid']))

(defn subst
  ([t x u] (subst t {x u}))
  ([t sub]
   (let [forbid (set/union
                 (apply set/union (map vars (vals sub)))
                 (into #{} (keys sub))
                 (free-vars t))
         [t' _] (subst- t sub forbid {})]
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

(example
 (subst '(λ [x ✳] (test x y (λ [x ✳] (test x y z)) y)) {'x ':replace})
 => '(λ [x' ✳] (test x' y (λ [x'' ✳] (test x'' y z)) y)))

(example
 (subst '(λ [x ✳] (test x y (λ [x ✳] (test x y x')) y)) {'x :replace-x
                                                        'x' :replace-x' })
 => '(λ [x'' ✳] (test x'' y (λ [x''' ✳] (test x''' y :replace-x')) y)))

(example
 (subst '(test x y (λ [x ✳] (test x y x')) y) {'x :replace-x
                                               'x' :replace-x' })
 => '(test :replace-x y (λ [x'' ✳] (test x'' y :replace-x')) y))

(example ;; XXX: this comes from a very subtile bug !
 (subst '(Π [⇧ (Π [x' T] (Π [⇧ (Π [x T] (Π [⇧ [X x]] [[R x] x']))] [R z]))]
            [R z]) 'z 'x)
 => '(Π [⇧ (Π [x' T] (Π [⇧' (Π [x'' T] (Π [⇧'' [X x'']] [[R x''] x']))] [R x]))] [R x]))

;;{
;; ## Locally nameless conversion
;;}

(defn nameless
  ([t] (nameless t 0 {}))
  ([t level bmap]
   (cond
     (variable? t) (if-let [k (get bmap t)]
                     (ln/mk-bvar (- level (inc k)))
                     (ln/mk-fvar t))
     (binder? t) (let [[b [x ty] body] t
                       ty' (nameless ty level bmap)
                       body' (nameless body
                                       (inc level)
                                       (assoc bmap x level))]
                   (case b
                     λ (ln/mk-lambda ty' body')
                     Π (ln/mk-prod ty' body')
                     (throw (ex-info "Wrong binder (please report)" {:binder b}))))
     (app? t) (let [[left right] t
                    left' (nameless left level bmap)
                    right' (nameless right level bmap)]
                (ln/mk-app left' right'))
     (ref? t) (let [[name & args] t
                    args' (map #(nameless % level bmap) args)]
                (ln/mk-ref name args'))
     :else t)))

(example
 (ln/unparse
  (nameless '(λ [x ✳] (λ [y ✳] [[x y] z]))))
 => '(λ [_1 ✳] (λ [_2 ✳] [[_1 _2] z])))

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

(defn alpha-eq?
  "Redefine as a multi-arity fn if the variadic implementation is too slow"
  #_([t1] true)
  #_([t1 t2] (= (alpha-norm t1) (alpha-norm t2)))
  #_([t1 t2 & more] (apply = (map alpha-norm (apply list t1 t2 more))))
  [t1 t2 & more] (apply = (map alpha-norm (apply list t1 t2 more))))

;; it's longer this way...
;; (defn alpha-eq? [t1 t2]
;;   (= (nameless t1)
;;      (nameless t2)))

(example
 (alpha-eq? '(λ [x ✳] x)
            '(λ [x ✳] x)
            '(λ [y ✳] y)) => true)

