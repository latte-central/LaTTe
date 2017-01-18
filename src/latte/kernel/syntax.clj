
(ns latte.kernel.syntax
  "This is an alternative representation of terms
using a locally-nameless approach."
  (:require [clj-by.example :refer [example do-for-example]]
            [clojure.set :as set]))

(def +examples-enabled+ true)

(defn kind? [t]
  (= t '□))

(defn type? [t]
  (= t '✳))

(defn sort? [t]
  (or (kind? t)
      (type? t)))

(defprotocol Term
  "The generic functions for terms."
  (free-vars [t]
    "The free variable symbols of term `t`.")
  (open-term [t k x]
    "Open the term `t` at level `k` with variable `x` ")
  (close-term [t k x]
    "Close the term `t` at level `k` for free variable named `x`")
  (subst-term [t s]
    "Apply substitution `s` to type `t`.")
  (apply-to-term [t k u]
    "Apply term `u` to term `t` at level `k` (in beta-reduction)")
  (unparse-term [t k bmap forbid]
    "Unparse term `t` at level `k` with `bmap` map of bound variable and `forbid`den names.")
  (unparse-ln-term [t]
    "Unparse as locally-nameless term `t`."))

(defn open
  "Open term `t` with variable `x`."
  [t x]
  (open-term t 0 x))

(defn close
  "Close term `t` for free variable named `x`."
  [t x]
  (close-term t 0 x))

(defn subst
  "Apply substitution `s` to type `t`."
  ([t x u] (subst-term t {x u}))
  ([t s] (subst-term t s)))

(defn apply-to
  "Apply term `u` to term `t` at level `k` (in beta-reduction)."
  ([t u] (apply-to-term t 0 u))
  ([t k u] (apply-to-term t k u)))

(defn unparse
  "Unparse term `t`."
  [t]
  (unparse-term t 0 {} (free-vars t)))

(defn unparse-ln
  "Unparse term `t` in a locally-nameless way."
  [t]
  (unparse-ln-term t))

(extend-type java.lang.Object
  Term
  ;; no free variables by default
  (free-vars [_] #{})
  ;; the default opening and closing are identity
  (open-term [t _ _] t)
  (close-term [t _ _] t)
  (subst-term [t _] t)
  (apply-to-term [t a b] t)
  ;; the default unparse is identity
  (unparse-term [t _ _ _] t)
  (unparse-ln-term [t] t))

(example
 ;; remark: changing a protocol extension
 ;; often requires a (cider) restart (because of the cache).
 (apply-to-term 'toto 'a 'b) => 'toto)

(defn mk-fresh
  ([base forbid] (mk-fresh base 0 forbid))
  ([base level forbid]
   (if-not (contains? forbid base)
     base
     (let [suffix (case level
                    0 ""
                    1 "'"
                    2 "''"
                    3 "'''"
                    (str "-" level))
           candidate (symbol (str base suffix))]
       (if (contains? forbid candidate)
         (recur base (inc level) forbid)
         candidate)))))

(example
 (mk-fresh 'x '#{x1 x2}) => 'x)

(example
 (mk-fresh 'x '#{x x' x''}) => 'x''')

(example
 (mk-fresh 'x '#{x x' x'' x'''}) => 'x-4)

(declare mk-bvar)
(defrecord FVar [name]
  Term
  (free-vars [t] #{(:name t)})
  (open-term [t _ _] t)
  (close-term [t k x] (if (= (:name t) x)
                        (mk-bvar k)
                        t))
  (subst-term [t s] (if-let [u (get s (:name t))]
                      u
                      t))
  (unparse-term [t _ _ _] (:name t))
  (unparse-ln-term [t] (:name t)))

(defn mk-fvar [x] (->FVar x))

(defn fvar? [v]
  (instance? FVar v))

(defrecord BVar [index]
  Term
  (free-vars [t] #{})
  (open-term [t k x]
    (if (= (:index t) k)
      (mk-fvar x)
      t))
  (close-term [t _ _] t)
  (apply-to-term [t k u]
    ;; (println "[apply-to-term] t=" t "k=" k "u=" t)
    (if (= k (:index t))
      u
      t))
  (subst-term [t _] t)
  (unparse-term [t _ bmap _]
    (if-let [bname (get bmap (:index t))]
      bname
      (keyword (str (:index t)))))
  (unparse-ln-term [t]
    (keyword (str (:index t)))))

(defn mk-bvar [index]
  (->BVar index))

(defn bvar? [v]
  (instance? BVar v))

(example
 (open-term (mk-fvar 'x) 2 'y)
 => (mk-fvar 'x))

(example
 (close-term (mk-fvar 'x) 2 'x)
 => (mk-bvar 2))

(example
 (close-term (mk-fvar 'x) 2 'y)
 => (mk-fvar 'x))

(example
 (unparse (mk-fvar 'x)) => 'x)

(example
 (open-term (mk-bvar 2) 2 'y)
 => (mk-fvar 'y))

(example
 (open-term (mk-bvar 1) 2 'y)
 => (mk-bvar 1))

(example
 (close-term (mk-bvar 1) 1 'x)
 => (mk-bvar 1))

(example
 (unparse (mk-bvar 1)) => :1)

(defrecord Lambda [name type body]
  Term
  (free-vars [t] (free-vars (:body t)))
  (open-term [t k x]
    (->Lambda (mk-fresh (:name t) #{x}) (open-term (:type t) k x)
              (open-term (:body t) (inc k) x)))
  (close-term [t k x]
    (->Lambda (:name t) (close-term (:type t) k x)
              (close-term (:body t) (inc k) x)))
  (subst-term [t s]
    (->Lambda (:name t) (subst-term (:type t) s)
              (subst-term (:body t) s)))
  (apply-to-term [t k u]
    (->Lambda (:name t) (apply-to-term (:type t) k u)
              (apply-to-term (:body t) (inc k) u)))
  (unparse-term [t k bmap forbid]
    (let [name (mk-fresh (:name t) forbid)]
      (list 'λ [name (unparse-term (:type t) k bmap forbid)]
            (unparse-term (:body t)
                          (inc k)
                          (assoc bmap k name)
                          (conj forbid name)))))
  (unparse-ln-term [t]
    (list 'λ [(unparse-ln-term (:type t))]
          (unparse-ln-term (:body t)))))

(defn mk-lambda [name type body]
  (->Lambda name type body))

(defn lambda? [v]
  (instance? Lambda v))

(example
 (open-term (mk-lambda 'x '□ (mk-bvar 3)) 2 'y)
 => (mk-lambda 'x '□ (mk-fvar 'y)))

(example
 (close-term (mk-lambda 'x '□ (mk-fvar 'y)) 2 'y)
 => (mk-lambda 'x '□ (mk-bvar 3)))

(example
 (unparse (mk-lambda 'x '□ (mk-bvar 0)))
 => '(λ [x □] x))

(example
 (unparse (mk-lambda 'x '□ (mk-bvar 1)))
 => '(λ [x □] :1))

(defrecord Prod [name type body]
  Term
  (free-vars [t] (free-vars (:body t)))
  (open-term [t k x]
    (->Prod (mk-fresh (:name t) #{x}) (open-term (:type t) k x)
              (open-term (:body t) (inc k) x)))
  (close-term [t k x]
    (->Prod (:name t) (close-term (:type t) k x)
            (close-term (:body t) (inc k) x)))
  (subst-term [t s]
    (->Prod (:name t) (subst-term (:type t) s)
              (subst-term (:body t) s)))
  (apply-to-term [t k u]
    (->Prod (:name t) (apply-to-term (:type t) k u)
              (apply-to-term (:body t) (inc k) u)))
  (unparse-term [t k bmap forbid]
    (let [name (mk-fresh (:name t) forbid)]
      (list 'Π [name (unparse-term (:type t) k bmap forbid)]
            (unparse-term (:body t)
                          (inc k)
                          (assoc bmap k name)
                          (conj forbid name)))))
  (unparse-ln-term [t]
    (list 'Π [(unparse-ln-term (:type t))]
          (unparse-ln-term (:body t)))))

(defn mk-prod [name type body]
  (->Prod name type body))

(defn prod? [v]
  (instance? Prod v))

(example
 (open-term (mk-prod 'x '□ (mk-bvar 3)) 2 'y)
 => (mk-prod 'x '□ (mk-fvar 'y)))

(example
 (close-term (mk-prod 'x '□ (mk-fvar 'y)) 2 'y)
 => (mk-prod 'x '□ (mk-bvar 3)))

(example
 (unparse (mk-prod 'x '□ (mk-bvar 0)))
 => '(Π [x □] x))

(example
 (unparse (mk-prod 'x '□ (mk-bvar 1)))
 => '(Π [x □] :1))

(defn binder? [v]
  (or (prod? v)
      (lambda? v)))

(defn binder-kind [t]
  (cond
    (lambda? t) :lambda
    (prod? t) :prod
    :else (throw (ex-info "Not a binder (please report)" {:term t}))))

(defn binder-fn [t]
  (case (binder-kind t)
    :lambda mk-lambda
    :prod mk-prod))

(declare app?)
(defrecord App [left right]
  Term
  (free-vars [t]
    (clojure.set/union (free-vars (:left t))
                       (free-vars (:right t))))
  (open-term [t k x]
    (->App (open-term (:left t) k x)
           (open-term (:right t) k x)))
  (close-term [t k x]
    (->App (close-term (:left t) k x)
           (close-term (:right t) k x)))
  (subst-term [t s]
    (->App (subst-term (:left t) s)
           (subst-term (:right t) s)))
  (apply-to-term [t k u]
    (->App (apply-to-term (:left t) k u)
           (apply-to-term (:right t) k u)))
  (unparse-term [t k bmap forbid]
    (let [left (unparse-term (:left t) k bmap forbid)
          right (unparse-term (:right t) k bmap forbid)]
      (if (app? (:left t))
        (concat left (list right))
        (list left right))))
  (unparse-ln-term [t]
    (let [left (unparse-ln-term (:left t))
          right (unparse-ln-term (:right t))]
      (if (app? (:left t))
        (concat left (list right))
        (list left right)))))

(defn mk-app
  ([right] right)
  ([left right & others]
   (let [app (->App left right)]
     (if (seq others)
       (apply mk-app app others)
       app))))

(example (mk-app 'x) => 'x)

(example
 (mk-app 'a 'b) => '#latte.kernel.syntax.App{:left a, :right b})

(example
 (mk-app 'a 'b 'c)
 => '#latte.kernel.syntax.App{:left #latte.kernel.syntax.App{:left a, :right b},
                               :right c})

(example
 (mk-app 'a 'b 'c 'd)
 => '#latte.kernel.syntax.App{:left #latte.kernel.syntax.App{:left #latte.kernel.syntax.App{:left a, :right b},
                                                               :right c},
                               :right d})

(defn app? [v]
  (instance? App v))

(example
 (app? (mk-app 'x 'y)) => true)

(example
 (app? (mk-lambda 'x 'ty 'x)) => false)

(example
 (app? '(1 2)) => false)

(example
 (free-vars (mk-app (mk-fvar 'x)
                    (mk-fvar 'y)))
 => '#{x y})

(example
 (unparse
  (open (mk-app (mk-lambda 'x '□ (mk-app (mk-bvar 1)
                                         (mk-bvar 0)))
                (mk-bvar 0)) 'z))
 => '((λ [x □] (z x)) z))

(example
 (unparse
  (open (mk-app (mk-lambda 'x '□ (mk-app (mk-bvar 1)
                                         (mk-bvar 0)))
                (mk-bvar 0)) 'x))
 => '((λ [x' □] (x x')) x))

(example
 (unparse
  (close (mk-app (mk-lambda 'x '□ (mk-app (mk-fvar 'x)
                                          (mk-fvar 'x)))
                 (mk-bvar 0)) 'x))
 => '((λ [x □] (:1 :1)) :0))

(example
 (unparse
  (close (mk-app (mk-lambda 'x '□ (mk-app (mk-fvar 'x)
                                          (mk-fvar 'z)))
                 (mk-bvar 0)) 'z))
 => '((λ [x' □] (x :1)) :0))

(example
 (unparse
  (mk-app 'x 'y (mk-app 'z 't)))
 => '(x y (z t)))


(defrecord Ref [name args]
  Term
  (free-vars [t] (apply set/union (map free-vars (:args t))))
  (open-term [t k x]
    (->Ref (:name t) (mapv #(open-term % k x) (:args t))))
  (close-term [t k x]
    (->Ref (:name t) (mapv #(close-term % k x) (:args t))))
  (subst-term [t s]
    (->Ref (:name t) (mapv #(subst-term % s) (:args t))))
  (apply-to-term [t k u]
    (->Ref (:name t) (mapv #(apply-to-term % k u) (:args t))))
  (unparse-term [t k bmap forbid]
    (list* (:name t) (map #(unparse-term % k bmap forbid) (:args t))))
  (unparse-ln-term [t]
    (list* (:name t) (map unparse-ln-term (:args t)))))

(defn mk-ref [name args]
  (->Ref name args))

(defn ref? [v]
  (instance? Ref v))

(example
 (unparse-ln-term (open-term (mk-ref 'ref [(mk-bvar 2) (mk-fvar 'z) (mk-bvar 4)]) 2 'y))
 => '(ref y z :4))

(example
 (unparse-ln-term (close-term (mk-ref 'ref [(mk-lambda 'x '□ (mk-fvar 'y)) (mk-fvar 'y)]) 2 'y))
 => '(ref (λ [□] :3) :2))


(defn alpha-eq? [t1 t2]
  (= (unparse-ln-term t1)
     (unparse-ln-term t2)))

(example
 (alpha-eq? (mk-lambda 'x '✳ (mk-bvar 0))
            (mk-lambda 'y '✳ (mk-bvar 0))) => true)


