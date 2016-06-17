(ns latte.typing
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [latte.syntax :as stx])
  (:require [latte.norm :as norm])
  )

(def ^:private +examples-enabled+)

;;{
;; # Type checking
;;}

;;{
;; ## Type environment
;;}

(defn env-fetch [env x]
  (if (seq env)
    (if (= (first (first env)) x)
      (second (first env))
      (recur (rest env) x))
    nil))

(defn env-put [env x t]
  (conj env [x t]))

(defn mk-env [& args]
  args)


;;{
;; ## Synthesis rules
;;}

(declare type-of-type
         type-of-var
         type-of-prod
         type-of-abs
         type-of-app
         type-of-ref)

(defn type-of [def-env env t]
  (cond
    (stx/kind? t) [:ko {:msg "Kind has not type" :term t}]
    (stx/type? t) (type-of-type)
    (stx/variable? t) (type-of-var def-env env t)
    ;; binders (lambda, prod)
    (stx/binder? t)
    (let [[binder [x ty] body] t]
      (case binder
        lambda (type-of-abs def-env env x ty body)
        prod (type-of-prod def-env env x ty body)
        (throw (ex-info "No such binder (please report)" {:term t :binder binder}))))
    ;; applications
    (stx/app? t) (type-of-app def-env env (first t) (second t))
    ;; references
    (stx/ref? t) (type-of-ref def-env env (first t) (rest t))
    :else
    (throw (ex-info "Invalid term (please report)" {:term t}))))

(example
 (type-of {} [] :kind) => [:ko {:msg "Kind has not type" :term :kind}])

(defn type-check? [def-env env term type]
  (let [[status type'] (type-of def-env env term)]
    (if (= status :ok)
      (norm/delta-beta-eq? def-env type type')
      (throw (ex-info "Cannot check type of term" {:term term})))))

;;{
;;
;;     --------------------
;;     E |- Type ::> Kind
;;}

(defn type-of-type []
  [:ok :kind])

(example
 (type-of {} [] :type) => [:ok :kind])

;;{
;;        ty::>Type or t::>Kind in E
;;     ------------------------------
;;        E,x::ty |- x ::> ty
;;}

(defn type-of-var [def-env env x]
  (if-let [ty (env-fetch env x)]
    (let [[status sort] (type-of def-env env ty)]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort}]
        (if (stx/sort? sort)
          [:ok ty]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x :type ty :sort sort}])))
    [:ko {:msg "No such variable in type environment" :term x}]))

(example
 (type-of {} '[[bool :type] [x bool]] 'x) => '[:ok bool])

(example
 (type-of {} '[[x bool]] 'x)
 => '[:ko {:msg "Cannot calculate type of variable.",
           :term x,
           :from {:msg "No such variable in type environment", :term bool}}])

(example
 (type-of {} '[[bool :type] [y bool]] 'x)
 => '[:ko {:msg "No such variable in type environment", :term x}])

;;{
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod [def-env env x A B]
  (let [[status sort1] (type-of def-env env A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term A :from sort1}]
      (let [sort1' (norm/normalize def-env sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)" :term A :type sort1}]
          (let [env' (env-put env x A)
                [status sort2] (type-of def-env env' B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product." :term B :from sort2}]
              (let [sort2' (norm/normalize def-env sort2)]
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (super-type not a sort)" :term B :type sort2}]
                  [:ok sort2'])))))))))

(example
 (type-of {} [] '(prod [x :type] x)) => [:ok :type])

(example
 (type-of {} [] '(prod [x :type] :type)) => [:ok :kind])

(example
 (type-of {} [] '(prod [x :kind] :type))
 => '[:ko {:msg "Cannot calculate domain type of product.", :term :kind,
           :from {:msg "Kind has not type" :term :kind}}])

(example
 (type-of {} [] '(prod [x :type] :kind))
 => '[:ko {:msg "Cannot calculate codomain type of product.", :term :kind,
           :from {:msg "Kind has not type" :term :kind}}])

;;{
;;    E,x:A |- t ::> B  E |- prod x:A. B ::> s
;;    --------------------------------------------
;;    E |- lambda x:A . t  ::>  prod x:A . B
;;}

(defn type-of-abs [def-env env x A t]
  (let [env' (env-put env x A)
        [status B] (type-of def-env env' t)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate codomain type of abstraction."
            :term (list 'lambda [x A] t) :from B}]
      (let [tprod (list 'prod [x A] B)
            [status sort] (type-of def-env env tprod)]
        (if (= status :ko)
          [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                :term (list 'lambda [x A] t)
                :codomain B :from sort}]
          (if (not (stx/sort? (norm/normalize def-env sort)))
            [:ko {:msg "Not a valid codomain type in abstraction (super-type not a sort)."
                  :term (list 'lambda [x A] t)
                  :codomain B
                  :type sort}]
            [:ok tprod]))))))

(example
 (type-of {} '[[bool :type] [t bool] [y bool]]
          '(lambda [x bool] x))
 => '[:ok (prod [x bool] bool)])

(example
 (type-of {} [] '(lambda [x :type] x)) => '[:ok (prod [x :type] :type)])

(example
 (type-of {} '[[y bool]] '(lambda [x bool] x))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (lambda [x bool] x),
           :from {:msg "Cannot calculate type of variable.", :term x,
                  :from {:msg "No such variable in type environment", :term bool}}}])

(example
 (type-of {} '[[y :type] [z y]] '(lambda [x z] x))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (lambda [x z] x),
           :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}])

(example
 (type-of {} '[[y bool]] '(lambda [x :type] y))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (lambda [x :type] y),
           :from {:msg "Cannot calculate type of variable.", :term y,
                  :from {:msg "No such variable in type environment", :term bool}}}])

(example
 (type-of {} '[[y bool]] '(lambda [x :type] :kind))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (lambda [x :type] :kind),
           :from {:msg "Kind has not type" :term :kind}}])

(example
 (type-of {} '[[y bool]] '(lambda [x :type] :type))
 => '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
           :term (lambda [x :type] :type), :codomain :kind,
           :from {:msg "Cannot calculate codomain type of product.", :term :kind,
                  :from {:msg "Kind has not type", :term :kind}}}])
(example
 (type-of {} '[[w :type] [y w] [z y]] '(lambda [x :type] z))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (lambda [x :type] z),
           :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}])

;;{
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app [def-env env rator rand]
  (let [[status trator] (type-of def-env env rator)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate operator (left-hand) type in application."
            :term [rator rand] :from trator}]
      (let [trator' (norm/normalize def-env trator)]
        (if (not (stx/prod? trator'))
          [:ko {:msg "Not a product type for operator (left-hand) in application." :term [rator rand] :operator-type trator}]
          (let [[_ [x A] B] trator']
            (if (not (type-check? def-env env rand A))
              [:ko {:msg "Cannot apply: type mismatch" :term [rator rand] :domain A :operand rand}]
              [:ok (stx/subst B x rand)])))))))


(example
 (type-of {} '[[bool :type] [y bool]]
          '[(lambda [x bool] x) y])
 => '[:ok bool])


;;{
;;    D |- ref :: [x1 t1] [x2 t2] ... [xN tN] -> t
;;    E |- e1 :: t1   E, x1:t1 |- e2 :: t2
;;    ...
;;    E, x1:t1, ..., xM-1:tM-1 |- eM :: tM
;; -------------------------------------------------------------------------------------
;;      D, E |- (ref e1 e2 ... eM)
;;              ::> (prod [xM+1 tM+1] ... (prod [xN tN] t [e1/x1, e2/x2, ...eM/xM]) ...)
;;}

