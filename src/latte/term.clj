
;;{
;;
;; # LaTTe : Representation of lambda-terms
;;
;; The `latte.term` namespace implements the
;; basic terms of type theory.
;;
;;}

(ns latte.term
  (:require [latte.utils :refer [example]]))

(def ^:dynamic *examples-enabled*) ;; activate examples
            
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
;;  of level 0 and each universe of level $n$ sits in a universe of level $n+1$.

;;}


(defrecord Univ [^int level])

(defn mk-univ [level]
  (->Univ level))

(example (:level (mk-univ 2)) => 2)

