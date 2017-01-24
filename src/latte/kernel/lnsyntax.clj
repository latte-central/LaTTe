
(ns latte.kernel.lnsyntax
  "This is an alternative representation of terms
using a locally-nameless approach.
  This requires a parse/unparse interface and thus it is
more cumbersome than using the standard terms.

  However some algorithms become quite simple with this
representation (others become awful, hence it is not
generalized), especially alpha-convertibility."
  (:require [clj-by.example :refer [example do-for-example]]))

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
    "Unparse term `t` at level `k` with `bmap` map of bound variable and `forbid`den names."))

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
  (do ;; #dbg
    (unparse-term t 0 {} (free-vars t))))

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
  (unparse-term [t _ _ _] t))

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
  (apply-to-term [t _ _] t)
  (unparse-term [t _ _ _] (:name t)))

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
  (unparse-term [t level bmap _]
    (if-let [bname (get bmap (- level (inc (:index t))))]
      bname
      (keyword (str (:index t))))))


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

(defrecord Lambda [type body]
  Term
  (free-vars [t] (free-vars (:body t)))
  (open-term [t k x]
    (->Lambda (open-term (:type t) k x)
              (open-term (:body t) (inc k) x)))
  (close-term [t k x]
    (->Lambda (close-term (:type t) k x)
              (close-term (:body t) (inc k) x)))
  (subst-term [t s]
    (->Lambda (subst-term (:type t) s)
              (subst-term (:body t) s)))
  (apply-to-term [t k u]
    (->Lambda (apply-to-term (:type t) k u)
              (apply-to-term (:body t) (inc k) u)))
  (unparse-term [t k bmap forbid]
    (let [name (mk-fresh (symbol (str "_" (inc k))) forbid)]
      (list 'λ [name (unparse-term (:type t) k bmap forbid)]
            (unparse-term (:body t)
                          (inc k)
                          (assoc bmap k name)
                          (conj forbid name))))))

(defn mk-lambda [type body]
  (->Lambda type body))

(defn lambda? [v]
  (instance? Lambda v))

(example
 (open-term (mk-lambda '□ (mk-bvar 3)) 2 'y)
 => (mk-lambda '□ (mk-fvar 'y)))

(example
 (close-term (mk-lambda '□ (mk-fvar 'y)) 2 'y)
 => (mk-lambda '□ (mk-bvar 3)))

(example
 (unparse (mk-lambda '□ (mk-bvar 0)))
 => '(λ [_1 □] _1))

(example
 (unparse (mk-lambda '□ (mk-bvar 1)))
 => '(λ [_1 □] :1))

(defrecord Prod [type body]
  Term
  (free-vars [t] (free-vars (:body t)))
  (open-term [t k x]
    (->Prod  (open-term (:type t) k x)
             (open-term (:body t) (inc k) x)))
  (close-term [t k x]
    (->Prod (close-term (:type t) k x)
            (close-term (:body t) (inc k) x)))
  (subst-term [t s]
    (->Prod (subst-term (:type t) s)
            (subst-term (:body t) s)))
  (apply-to-term [t k u]
    (->Prod (apply-to-term (:type t) k u)
            (apply-to-term (:body t) (inc k) u)))
  (unparse-term [t k bmap forbid]
    (let [name (mk-fresh (symbol (str "_" (inc k))) forbid)]
      (list 'Π [name (unparse-term (:type t) k bmap forbid)]
            (unparse-term (:body t)
                          (inc k)
                          (assoc bmap k name)
                          (conj forbid name))))))

(defn mk-prod [type body]
  (->Prod type body))

(defn prod? [v]
  (instance? Prod v))

(example
 (open-term (mk-prod '□ (mk-bvar 3)) 2 'y)
 => (mk-prod '□ (mk-fvar 'y)))

(example
 (close-term (mk-prod '□ (mk-fvar 'y)) 2 'y)
 => (mk-prod '□ (mk-bvar 3)))

(example
 (unparse (mk-prod '□ (mk-bvar 0)))
 => '(Π [_1 □] _1))

(example
 (unparse (mk-prod '□ (mk-bvar 1)))
 => '(Π [_1 □] :1))

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
      [left right])))

(defn mk-app [left right]
  (->App left right))

(example
 (mk-app 'a 'b) => '#latte.kernel.lnsyntax.App{:left a, :right b})

(defn app? [v]
  (instance? App v))

(example
 (app? (mk-app 'x 'y)) => true)

(example
 (app? (mk-lambda 'ty 'x)) => false)

(example
 (app? '(1 2)) => false)

(example
 (free-vars (mk-app (mk-fvar 'x)
                    (mk-fvar 'y)))
 => '#{x y})

(example
 (unparse
  (open (mk-app (mk-lambda '□ (mk-app (mk-bvar 1)
                                      (mk-bvar 0)))
                (mk-bvar 0)) 'z))
 => '((λ [_1 □] (z _1)) z))

(example
 (unparse
  (open (mk-app (mk-lambda '□ (mk-app (mk-bvar 1)
                                      (mk-bvar 0)))
                (mk-bvar 0)) 'x))
 => '((λ [_1 □] (x _1)) x))

(example
 (unparse
  (close (mk-app (mk-lambda '□ (mk-app (mk-fvar 'x)
                                       (mk-fvar 'x)))
                 (mk-bvar 0)) 'x))
 => '((λ [_1 □] (:1 :1)) :0))

(example
 (unparse
  (close (mk-app (mk-lambda '□ (mk-app (mk-fvar 'x)
                                       (mk-fvar 'z)))
                 (mk-bvar 0)) 'z))
 => '((λ [_1 □] (x :1)) :0))

(example
 (unparse
  (mk-app (mk-app 'x 'y) (mk-app 'z 't)))
 => '[[x y] [z t]])


(example
 (unparse (mk-lambda '□
                     (mk-lambda '□ (mk-app (mk-app (mk-bvar 0) (mk-bvar 1)) (mk-bvar 2)))))
 => '(λ [_1 □] (λ [_2 □] [[_2 _1] :2])))

(defrecord Ref [name args]
  Term
  (free-vars [t] (apply clojure.set/union (map free-vars (:args t))))
  (open-term [t k x]
    (->Ref (:name t) (mapv #(open-term % k x) (:args t))))
  (close-term [t k x]
    (->Ref (:name t) (mapv #(close-term % k x) (:args t))))
  (subst-term [t s]
    (->Ref (:name t) (mapv #(subst-term % s) (:args t))))
  (apply-to-term [t k u]
    (->Ref (:name t) (mapv #(apply-to-term % k u) (:args t))))
  (unparse-term [t k bmap forbid]
    (list* (:name t) (map #(unparse-term % k bmap forbid) (:args t)))))

(defn mk-ref [name args]
  (->Ref name args))

(defn ref? [v]
  (instance? Ref v))

(example
 (unparse (open-term (mk-ref 'ref [(mk-bvar 2) (mk-fvar 'z) (mk-bvar 4)]) 2 'y))
 => '(ref y z :4))

;; some examples involving lambda and application

(example
 (unparse (mk-lambda  '✳
                      (close-term (mk-lambda (mk-lambda  (mk-fvar 'A)
                                                         (mk-lambda  (mk-fvar 'B)
                                                                     (mk-fvar 'C)))
                                            (mk-app (mk-bvar 0) (mk-fvar 'x)))
                                  0 'C)))
 => '(λ [_1 ✳] (λ [_2 (λ [_2 A] (λ [_3 B] _1))] (_2 x))))



(defn alpha-eq? [t1 t2]
  (= t1 t2))




