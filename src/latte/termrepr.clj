
(ns latte.termrepr)

;;{
;;
;; # LaTTe : Representation of lambda-terms
;;
;; The syntax of the CommonTypes lambda-terms is as follows:
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
;; Each syntactic constructor is implemented as a separate class.
;;
;;}


