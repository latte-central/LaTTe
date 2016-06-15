
(ns latte.syntax
  (:require [clj-by.example :refer [example do-for-example]])
  )

;;{
;; # The syntax of type theory
;;}

(def ^:private +examples-enabled+)

;;{
;; ## Lambda terms
;;}

(defn kind? [t]
  (= t :kind))

(defn type? [t]
  (= t :type))

(defn sort? [t]
  (or (kind? t)
      (type? t)))

(defn var? [t]
  (symbol? t))

(defn binder? [t]
  (and (list? t)
       (contains? '#{lambda prod} (first t))))

(defn app? [t]
  (and (vector? t)
       (= (count t) 2)))

(defn ref? [t]
  (and (list? t)
       (not (contains? '#{lambda prod} (first t)))))

;;{
;; ## Free and bound variables
;;}

(defn free-vars [t]
  (cond
    (var? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (clojure.set/union (free-vars ty)
                                     (disj (free-vars body) x)))
    (app? t) (clojure.set/union (free-vars (first t))
                                (free-vars (second t)))
    (ref? t) (apply clojure.set/union (map free-vars (rest t)))
    :else #{}))

(example
 (free-vars 'x) => #{'x})

(example
 (free-vars '[x y]) => #{'x 'y})

(example
 (free-vars '(lambda [x t] [x [y z]])) => #{'t 'y 'z})

(example
 (free-vars '(prod [x t] [x [y z]])) => #{'t 'y 'z})

(example
 (free-vars '(lambda [x t] (test x y z))) => '#{t y z})

(defn vars [t]
  (cond
    (var? t) #{t}
    (binder? t) (let [[_ [x ty] body] t]
                  (clojure.set/union (vars ty) (vars body)))
    (app? t) (clojure.set/union (vars (first t))
                                (vars (second t)))
    (ref? t) (apply clojure.set/union (map vars (rest t)))
    :else #{}))

(example
 (vars 'x) => #{'x})

(example
 (vars '[x y]) => #{'x 'y})

(example
 (vars '(lambda [x t] (test x [y z]))) => #{'t 'x 'y 'z})

(example
 (vars '(prod [x t] (test x [y z]))) => #{'t 'x 'y 'z})

(defn bound-vars [t]
  (clojure.set/difference (vars t) (free-vars t)))

(example
 (bound-vars 'x) => #{})

(example
 (bound-vars '[x y]) => #{})

(example
 (bound-vars '(lambda [x t] (test x [y z]))) => #{'x})

(example
 (bound-vars '(lambda [x t] (test t [y z]))) => #{})

(example
 (bound-vars '(prod [x t] (test x [y z]))) => #{'x})

;;{
;; ## Substitution
;;}

(defn mk-fresh [base forbid]
  (if (contains? forbid base)
    (recur (symbol (str (name base) "'")) forbid)
    base))

(example
 (mk-fresh 'x '#{x x' x''}) => 'x''')

(defn subst-
  ([t sub] (subst- t sub #{}))
  ([t sub forbid]
   (cond
     (var? t) [(get sub t t) (conj forbid t)]
     (binder? t) (let [[binder [x ty] body] t
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
     (app? t) (let [[rator forbid'] (subst- (first t) sub forbid)
                    [rand forbid''] (subst- (second t) sub forbid')]
                [[rator rand] forbid''])
     (ref? t) (let [[args forbid'] (reduce (fn [[ts forbid] t]
                                             (let [[t' forbid'] (subst- t sub forbid)]
                                               [(conj ts t') forbid'])) ['() forbid] (rest t))]
                [(conj (into '() args) (first t)) forbid'])
     :else [t forbid])))

(defn subst [t sub]
  (let [[t' _] (subst- t sub #{})]
    t'))

(example
 (subst 'x {'x :type}) => :type)

(example
 (subst 'y {'x :type}) => 'y)

(example
 (subst '[y x] {'x :type}) => '[y :type])

(example
 (subst '[x (lambda [x :type] (test x y z))] {'x :type, 'y :kind})
 => '[:type (lambda [x' :type] (test x' :kind z))])
q
(example
 (subst '[x (prod [x :type] [y x])] {'x :type, 'y 'x})
 => '[:type (prod [x' :type] [x x'])])
;; and not: '(:type (prod [x :type] (x x)))


;;{
;; ## Alpha-equivalence
;;}

(defn alpha-norm- [[tag t] sub level]
  (case tag
    :var [(get sub t t) level]
    :bind (let [{binder :binder [x ty] :binding body :body} t
                x' (symbol (str "_" level))
                [ty' level'] (alpha-norm- ty sub (inc level))
                [body' level''] (alpha-norm- body (assoc sub x x') level')]
            [(list binder [x' ty'] body')
             level''])
    :app (let [[left' level'] (alpha-norm- (:left t) sub level)
               [right' level''] (alpha-norm- (:right t) sub level')]
           [(list left' right')
            level''])
    [t level]))

(defn alpha-norm [t]
  (let [[t' _] (alpha-norm- (validate ::term t) {} 1)]
    t'))

(example
 (alpha-norm 'x) => 'x)

(example
 (alpha-norm '(lambda [x :type] x))
 => '(lambda [_1 :type] _1))

(defn alpha-eq? [t1 t2]
  (= (alpha-norm t1)
     (alpha-norm t2)))

(example
 (alpha-eq? '(lambda [x :type] x)
            '(lambda [y :type] y)) => true)


(def alpha-eq-refl
  (prop/for-all
   [t (s/gen ::term)]
   (alpha-eq? t t)))

(example
 (:result (tc/quick-check 20 alpha-eq-refl)) => true)

;; Remark: symmetry and transitivity are harder to test...
