
;;{
;;
;; # LaTTe : Representation of lambda-terms
;;
;; The `latte.term` namespace implements the
;; basic terms of type theory.
;;
;;}

(ns latte.term
  (:require [clojure.set]
            [latte.utils :refer [example append]]
            [latte.alist :as alist :refer [acons vassoc]]
            [latte.termparser :as parser :refer [parse]]))

(def ^:dynamic *examples-enabled* true) ;; to activate in-line examples

;;{

;; ## Term protocols

;;}

(defprotocol Unparser
  "A protocol for Unparsing term representations
  as clojure expressions."
  (unparse
    [expr]
    "Produce a `parsable` clojure expression from `expr`
 in optional lexical environement `env`."))


(defprotocol FreeVars
  "A protocol for fetching the set of free variables."
  (free-vars
   [expr kind]
   "Return a set of the free variables of `expr` according 
to their kind: :product, :forall or :open."))

;;{
;;
;; ## Lambda-terms
;;
;; The syntax of the lambda-terms is as follows:
;;
;; term $\kappa,~\tau,~e$ ::= 
;;
;;   - univ$_i$                  (universe of level $i\geq 0$)
;;   - $x$                       (variable)
;;   - $e~e'$                    (application)
;;   - $\lambda x :: \tau.e$     (abstraction)
;;   - $\forall x :: \tau.\tau'$ (product)
;;   - $e$ :: $\tau$             (annotated term)
;;
;; Each syntactic constructor is implemented as a separate record.
;;
;;}


;;{

;; ### Universes

;; A *universe* is a set of types. The basic types are in the universe
;; of level 0 and each universe of level $n$ sits in a universe of level $n+1$.

;;}


(defrecord Univ [^int level])

(defn mk-univ
  "Make a universe of the given `level` (a natural number)."
  [level]
  (->Univ level))

(example (:level (mk-univ 2)) => 2)

(parser/register-term-list-parser
 'univ (fn [expr & _]
         (parser/parse-list-check-arity expr 1)
         (let [level (second expr)]
           (if (not (and (integer? level)
                         (>= level 0)))
             (throw (Exception. (str "Universe level must be positive, given: " level)))
             (mk-univ level)))))

(example (parse '(univ 2)) => (mk-univ 2))

(example (try
           (parse '(univ -1))
           (catch Exception e (.getMessage e)))
         => "Universe level must be positive, given: -1")

(example (try
           (parse '(univ 1 bad))
           (catch Exception e (.getMessage e)))
           => "Wrong arity: expect 1 argument for 'univ'-expressions, given: 2")

(defn- match-set-expr? [expr _]
  (and (symbol? expr)
       (= (name expr) "set")))

(parser/register-term-other-parser
 match-set-expr?
 (fn [expr bind-env]
   (mk-univ 0)))

(example (parse 'set) => (mk-univ 0))

(extend-type Univ
  Unparser
  (unparse
      [u] (list (symbol "univ") (:level u)))
  FreeVars
  (free-vars
   [_ _] #{}))

(example (unparse (mk-univ 2)) => '(univ 2))

(example (free-vars (mk-univ 2) :forall) => #{})

;;{

;; ### Applications

;; An application is a combination of an operator applied to a single operand.

;;}

(defrecord Application [rator rand])

(defn mk-application
  "Make an application of ope`rator` to ope`rand`."
  [rator rand]
  (->Application rator rand))

(example (let [app (mk-application (mk-univ 2) (mk-univ 3))]
           [ (:level (:rator app)) (:level (:rand app)) ])
         => [2 3])

(defn match-application-expr?
  [expr _]
  (and (list? expr)
       (>= (count expr) 2)))

(defn- binarize-application
  [expr]
  (cond
    (< (count expr) 2) (throw (IllegalArgumentException. "(< (count `expr`) 2) : please report"))
    (= (count expr) 2) (mk-application (first expr) (second expr))
    :else (recur (conj (next (next expr)) (mk-application (first expr) (second expr))))))

(example (binarize-application '(f a b c d))
         => (mk-application
             (mk-application
              (mk-application
               (mk-application 'f 'a)
               'b)
              'c)
             'd))


(parser/register-term-other-parser
 match-application-expr?
 (fn [expr bind-env]
   (binarize-application (map #(parse % bind-env) expr))))

(example (parse '((univ 1) (univ 2) (univ 3)))
         => (mk-application (mk-application (mk-univ 1) (mk-univ 2)) (mk-univ 3)))

(extend-type Application
  Unparser
  (unparse
    [app]
     (let [urator (unparse (:rator app))
           rator (if (instance? Application (:rator app)) urator (list urator))
           urand (unparse (:rand app))
           rand (if (instance? Application (:rand app)) urand (list urand))]
       (append rator rand)))
  FreeVars
  (free-vars
      [app kind] (clojure.set/union (free-vars (:rator app) kind) (free-vars (:rand app) kind))))

(example (unparse (parse '((univ 1) (univ 2))))
         => '((univ 1) (univ 2)))

(example (unparse (parse '((univ 1) (univ 2) (univ 3))))
         => '((univ 1) (univ 2) (univ 3)))

(example (unparse (parse '(((univ 1) (univ 2)) ((univ 3) (univ 4)))))
         => '((univ 1) (univ 2) (univ 3) (univ 4)))

(example (free-vars (parse '((univ 1) (univ 2) (univ 3))) :forall) => #{})

;;{

;; ### Abstractions

;; The $\lambda$-abstractions allow to define anonymous fonctions, such as
;; the identity function for a given type $\tau$, written as: $\lambda x:\tau.x$.


;;}

(defrecord Abstraction [var type body])


(defn mk-abstraction
  "Make an abstraction with variable `var` of type
  `type` bound within `body`."
  [var type body]
  (->Abstraction var type body))

(example (:var (mk-abstraction 'x '(univ 0) 'x)) => 'x)
(example (:type (mk-abstraction 'x '(univ 0) 'x)) => '(univ 0))
(example (:body (mk-abstraction 'x '(univ 0) 'x)) => 'x)

(parser/register-term-list-parser
 'lambda (fn [expr env]
           (parser/parse-list-check-arity expr 2)
           (let [[var etype] (second expr)
                 type (parse etype env)
                 body (parse (nth expr 2) (acons var :lambda env))]
             (if (not (symbol? var))
               (throw (Exception. (str "Abstraction variable is not a symbol: " var))))
             (mk-abstraction var type body))))

(example (:var (parse '(lambda [x (univ 2)] (univ 1)))) => 'x)

(example (:type (parse '(lambda [x (univ 2)] (univ 1)))) => (mk-univ 2))

(example (:body (parse '(lambda [x (univ 2)] (univ 1)))) => (mk-univ 1))

(example (try
           (parse '(lambda [1 (univ 1)] (univ 2)))
           (catch Exception e (.getMessage e)))
         => "Abstraction variable is not a symbol: 1")

(extend-type Abstraction
  Unparser
  (unparse
    [e]
     (list 'lambda [(:var e) (unparse (:type e))]
           (unparse (:body e))))
  FreeVars
  (free-vars
   [e kind] (clojure.set/union
             (free-vars (:type e) kind)
             (disj (free-vars (:body e) kind) (:var e)))))

(example (unparse (parse '(lambda [x (univ 1)] (univ 2))))
         => '(lambda [x (univ 1)] (univ 2)))

(example (free-vars (parse '(lambda [x (univ 1)] (univ 2))) :lambda)
         => #{})

;;{

;; ### Products

;; The product are the types of abstractions, and moreover represent
;; the universal quantification in logic.

;; For example, $\forall x:\tau.P$ makes $P$ (presumably a predicate)
;; true for any $x$ of type $\tau$.

;;}

(defrecord Product [var type body])

(defn mk-product
  "Make a product with variable `var` of type
  `type` bound within `body`."
  [var type body]
  (->Product var type body))

(example (:var (mk-product 'x '(univ 0) 'x)) => 'x)
(example (:type (mk-product 'x '(univ 0) 'x)) => '(univ 0))
(example (:body (mk-product 'x '(univ 0) 'x)) => 'x)

(parser/register-term-list-parser
 'forall (fn [expr env]
           (parser/parse-list-check-arity expr 2)
           (let [[var etype] (second expr)
                 type (parse etype env)
                 body (parse (nth expr 2) (acons var :forall env))]
             (if (not (symbol? var))
               (throw (Exception. (str "Product variable is not a symbol: " var))))
             (mk-product var type body))))

(example (:var (parse '(forall [x (univ 2)] (univ 1)))) => 'x)

(example (:type (parse '(forall [x (univ 2)] (univ 1)))) => (mk-univ 2))

(example (:body (parse '(forall [x (univ 2)] (univ 1)))) => (mk-univ 1))

(example (try
           (parse '(forall [1 (univ 1)] (univ 2)))
           (catch Exception e (.getMessage e)))
         => "Product variable is not a symbol: 1")

(defonce implication-fake-variable (gensym))

(parser/register-term-list-parser
 '=> (fn [expr env]
       (parser/parse-list-check-arity expr 2)
       (let [type (parse (second expr) env)
             body (parse (nth expr 2) env)]
         (mk-product implication-fake-variable type body))))

(example (:var (parse '(=> (univ 2) (univ 1)))) => implication-fake-variable)

(example (:type (parse '(forall [x (univ 2)] (univ 1)))) => (mk-univ 2))

(example (:body (parse '(forall [x (univ 2)] (univ 1)))) => (mk-univ 1))

(extend-type Product
  Unparser
  (unparse
   [e]
   (if (= (:var e) implication-fake-variable)
     (list '=> (unparse (:type e)) (unparse (:body e)))
     (list 'forall [(:var e) (unparse (:type e))]
           (unparse (:body e)))))
  FreeVars
  (free-vars
      [e kind] (clojure.set/union
                (free-vars (:type e) kind)
                (disj (free-vars (:body e) kind) (:var e)))))


(example (unparse (parse '(forall [x (univ 1)] (univ 2))))
         => '(forall [x (univ 1)] (univ 2)))

(example (free-vars (parse '(forall [x (univ 1)] (univ 2))) :forall)
         => #{})

;;{

;; ### Variables

;; In general, we distinguish among :

;;   - symbolic constants, or *names*,
;;   - free occurrences of variables, or *free variables*,
;;   - bound occurrences of variables, or *bound variables* within
;;     the scope of a *binder*, either a $lambda$-abstraction or a product.

;; For constants and free variables, we rely on our host language,
;; thus we do not interprete these directly.
;; We only consider explicit representation for lambda and product
;; variables

;;}

;;{

;; #### Abstraction variables

;;}

(defrecord LambdaVar [name])

(defn mk-lambda-var
  "Make the `name` variable bound within a lambda."
  [name]
  (->LambdaVar name))

(example (:name (mk-lambda-var 'my-var))
         => 'my-var)

(defn- match-bound-var?
  [expr env kind]
   (and (symbol? expr)
        (let [binding (alist/assoc expr env)]
          (and binding
               (= (second binding) kind)))))

(defn- match-free-var?
  [expr env]
  (and (symbol? expr)
       (not (alist/assoc expr env))))

(defn- match-lambda-var?
  [expr env]
  (match-bound-var? expr env :lambda))
  
(parser/register-term-other-parser
 match-lambda-var?
 (fn [expr env]
   (mk-lambda-var expr)))

(example (parse 'my-var (list ['my-var :lambda]))
         => (mk-lambda-var 'my-var))

(example (parse '(lambda [x (univ 0)] x))
         => (mk-abstraction 'x (mk-univ 0) (mk-lambda-var 'x)))

(extend-type LambdaVar
  Unparser
  (unparse [e] (:name e))
  FreeVars
  (free-vars [e kind] (if (= kind :lambda)
                        #{(:name e)}
                        #{})))

(example (unparse (mk-lambda-var 'my-var)) => 'my-var)

(example (unparse (parse '(lambda [x (univ 0)] x)))
         => '(lambda [x (univ 0)] x))

(example (free-vars (:body (parse '(lambda [x (univ 0)] x))) :lambda)
         => #{'x})

(example (free-vars (:body (parse '(lambda [x (univ 0)] x))) :forall)
         => #{})

;;{

;; #### Product variables

;;}

(defrecord ProductVar [name])

(defn mk-product-var
  "Make the `name` variable bound within a forall."
  [name]
  (->ProductVar name))

(example (:name (mk-product-var 'my-var))
         => 'my-var)

(defn- match-product-var?
  [expr env]
  (match-bound-var? expr env :forall))

(parser/register-term-other-parser
 match-product-var?
 (fn [expr env]
   (mk-product-var expr)))

(example (parse 'my-var (list ['my-var :forall]))
         => (mk-product-var 'my-var))

(example (parse '(forall [x (univ 0)] x))
         => (mk-product 'x (mk-univ 0) (mk-product-var 'x)))

(extend-type ProductVar
  Unparser
  (unparse [e] (:name e))
  FreeVars
  (free-vars [e kind] (if (= kind :forall)
                        #{(:name e)}
                        #{})))

(example (unparse (mk-product-var 'my-var)) => 'my-var)

(example (unparse (parse '(forall [x (univ 0)] x)))
         => '(forall [x (univ 0)] x))


(example (free-vars (:body (parse '(forall [x (univ 0)] x))) :forall)
         => #{'x})

(example (free-vars (:body (parse '(forall [x (univ 0)] x))) :lambda)
         => #{})

;;{

;; #### Open variables

;; Open variables are open to substitution and/or binding
;; in some external environment.

;;}

(defrecord OpenVar [name])

(defn mk-open-var
  "Make the `name` variable free and open ."
  [name]
  (->OpenVar name))

(example (:name (mk-open-var 'my-var))
         => 'my-var)

(defn- match-open-var?
  [expr env]
  (match-free-var? expr env))

(parser/register-term-other-parser
 match-open-var?
 (fn [expr env]
   (mk-open-var expr)))

(example (parse 'my-var (list))
         => (mk-open-var 'my-var))

(example (parse '(forall [x (univ 0)] (x y)))
         => (mk-product 'x (mk-univ 0) (mk-application
                                        (mk-product-var 'x)
                                        (mk-open-var 'y))))

(extend-type OpenVar
  Unparser
  (unparse [e] (:name e))
  FreeVars
  (free-vars [e kind] (if (= kind :open)
                        #{(:name e)}
                        #{})))

(example (unparse (mk-open-var 'my-var)) => 'my-var)

(example (unparse (parse '(forall [x (univ 0)] y)))
         => '(forall [x (univ 0)] y))


(example (free-vars (parse '(forall [x (univ 0)] (x y))) :open)
         => #{'y})

(example (free-vars (:body (parse '(forall [x (univ 0)] (x y)))) :lambda)
         => #{})


