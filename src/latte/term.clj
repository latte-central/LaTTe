
;;{
;;
;; # LaTTe : Representation of lambda-terms
;;
;; The `latte.term` namespace implements the
;; basic terms of type theory.
;;
;;}

(ns latte.term
  (:require [latte.utils :refer [example]]
            [latte.termparser :as parser :refer [parse]]))

(def ^:dynamic *examples-enabled* true)

;;{

;; ## Term protocols

;;}

(defprotocol Unparser
  "A protocol for Unparsing term representations
  as clojure expressions."
  (unparse [expr] "Produce a `parsable` clojure expression from `expr`."))

;; (def ^:dynamic *examples-enabled* true) ;; to activate in-line examples
            
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

(extend-type Univ
  Unparser
  (unparse [u]
    (list (symbol "univ") (:level u))))

(example (unparse (mk-univ 2)) => '(univ 2))


;;{

;; ### Variables

;; In general, we distinguish among :

;;   - symbolic constants, or *names*,
;;   - free occurrences of variables, or *free variables*,
;;   - bound occurrences of variables, or *bound variables* within
;;     the scope of a *binder*.

;; For free variables, we use our host language, and we will thus
;; consider all symbolic names as constant (introduced as needed),
;; and otherwise all variables bound.

;; The two primitive binders are the `lambda` abstraction
;; and the dependent product `forall`, to be introduced later on.

;;}

(defrecord BoundVar [name])

(defn mk-bound-var
  "Make the `name` variable bound."
  [name]
  (->BoundVar name))

(example (:name (mk-bound-var 'my-var))
         => 'my-var)

;; (defn match-decl-var?
;;   [expr decl-env & _ ]
;;   (and (symbol? expr)
;;        (contains? decl-env expr)))

;; (parser/register-term-other-parser
;;  match-decl-var?
;;  (fn [expr & _]
;;    (mk-decl-var expr)))

;; (example (parse 'my-var {'my-var (mk-univ 0)} {} ())
;;          => (mk-decl-var 'my-var))

;; (extend-type DeclVar
;;   Unparser
;;   (unparse [var]
;;     (:name var)))

;; (example (unparse (mk-decl-var 'my-var)) => 'my-var)

;;{

;; #### Definition variables

;;}

;; TODO
