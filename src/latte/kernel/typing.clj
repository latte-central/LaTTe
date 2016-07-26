(ns latte.kernel.typing
  (:require [clj-by.example :refer [example do-for-example]])

  (:require [latte.kernel.utils :as u])
  (:require [latte.kernel.syntax :as stx])
  (:require [latte.kernel.norm :as norm])
  (:require [latte.kernel.defenv :as defenv])
  )

(def ^:private +examples-enabled+)

;;{
;; # Type checking
;;}

;;{
;; ## Type environment
;;}

(defn env-fetch [env x]
  ;; (println "[env-fetch] env=" env "x=" x)
  (if (seq env)
    (if (= (first (first env)) x)
      (second (first env))
      (recur (rest env) x))
    nil))

(defn env-put [env x t]
  (cons [x t] env))

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

(defn type-of-term [def-env env t]
  ;;(println "[type-of-term] env=" env " t=" t)
  (cond
    (stx/kind? t) [:ko {:msg "Kind has not type" :term t}]
    (stx/type? t) (type-of-type)
    (stx/variable? t) (type-of-var def-env env t)
    ;; binders (lambda, prod)
    (stx/binder? t)
    (let [[binder [x ty] body] t]
      (case binder
        λ (type-of-abs def-env env x ty body)
        Π (type-of-prod def-env env x ty body)
        (throw (ex-info "No such binder (please report)" {:term t :binder binder}))))
    ;; references
    (stx/ref? t) (type-of-ref def-env env (first t) (rest t))
    ;; applications
    (stx/app? t) (type-of-app def-env env (first t) (second t))
    :else
    (throw (ex-info "Invalid term (please report)" {:term t}))))

(example
 (type-of-term {} [] '□) => '[:ko {:msg "Kind has not type" :term □}])

(defn type-check? [def-env env term type]
  ;;(println "[type-check?] term=" term "type=" type)
  ;;(println "    ctx=" env)
  (let [[status type'] (type-of-term def-env env term)]
    ;;(println "  ==> " status "type'=" type' "vs. type=" type)
    (if (= status :ok)
      (norm/beta-delta-eq? def-env type type')
      (throw (ex-info "Cannot check type of term" {:term term :from type'})))))

;;{
;;
;;     --------------------
;;     E |- Type ::> Kind
;;}

(defn type-of-type []
  [:ok '□])

(example
 (type-of-term {} [] '✳) => '[:ok □])

;;{
;;        ty::>Type or t::>Kind in E
;;     ------------------------------
;;        E,x::ty |- x ::> ty
;;}

(defn type-of-var [def-env env x]
  (if-let [ty (env-fetch env x)]
    (let [[status sort] (type-of-term def-env env ty)]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort}]
        (if (stx/sort? sort)
          [:ok ty]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x :type ty :sort sort}])))
    [:ko {:msg "No such variable in type environment" :term x}]))

(example
 (type-of-term {} '[[bool ✳] [x bool]] 'x) => '[:ok bool])

(example
 (type-of-term {} '[[x bool]] 'x)
 => '[:ko {:msg "Cannot calculate type of variable.",
           :term x,
           :from {:msg "No such variable in type environment", :term bool}}])

(example
 (type-of-term {} '[[bool ✳] [y bool]] 'x)
 => '[:ko {:msg "No such variable in type environment", :term x}])

;;{
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod [def-env env x A B]
  (let [[status sort1] (type-of-term def-env env A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term A :from sort1}]
      (let [sort1' (norm/normalize def-env sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)" :term A :type sort1}]
          (let [env' (env-put env x A)
                [status sort2] (type-of-term def-env env' B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product." :term B :from sort2}]
              (let [sort2' (norm/normalize def-env sort2)]
                ;; (println "sort2' = " sort2' " sort? " (stx/sort? sort2'))
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (not a sort)" :term B :type sort2}]
                  [:ok sort2'])))))))))

(example
 (type-of-term {} [] '(Π [x ✳] x)) => '[:ok ✳])

(example
 (type-of-term {} [] '(Π [x ✳] ✳)) => '[:ok □])

(example
 (type-of-term {} [] '(Π [x □] ✳))
 => '[:ko {:msg "Cannot calculate domain type of product.", :term □,
           :from {:msg "Kind has not type" :term □}}])

(example
 (type-of-term {} [] '(Π [x ✳] □))
 => '[:ko {:msg "Cannot calculate codomain type of product.", :term □,
           :from {:msg "Kind has not type" :term □}}])

;;{
;;    E,x:A |- t ::> B  E |- prod x:A. B ::> s
;;    --------------------------------------------
;;    E |- lambda x:A . t  ::>  prod x:A . B
;;}

(defn type-of-abs [def-env env x A t]
  (let [env' (env-put env x A)
        [status B] (type-of-term def-env env' t)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate codomain type of abstraction."
            :term (list 'λ [x A] t) :from B}]
      (let [tprod (list 'Π [x A] B)
            [status sort] (type-of-term def-env env tprod)]
        (if (= status :ko)
          [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                :term (list 'λ [x A] t)
                :codomain B :from sort}]
          (if (not (stx/sort? (norm/normalize def-env sort)))
            [:ko {:msg "Not a valid codomain type in abstraction (super-type not a sort)."
                  :term (list 'λ [x A] t)
                  :codomain B
                  :type sort}]
            [:ok tprod]))))))

(example
 (type-of-term {} '[[bool ✳] [t bool] [y bool]]
          '(λ [x bool] x))
 => '[:ok (Π [x bool] bool)])

(example
 (type-of-term {} [] '(λ [x ✳] x)) => '[:ok (Π [x ✳] ✳)])

(example
 (type-of-term {} '[[y bool]] '(λ [x bool] x))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x bool] x),
           :from {:msg "Cannot calculate type of variable.", :term x,
                  :from {:msg "No such variable in type environment", :term bool}}}])

(example
 (type-of-term {} '[[y ✳] [z y]] '(λ [x z] x))

 
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x z] x),
           :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] y))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] y),
           :from {:msg "Cannot calculate type of variable.", :term y,
                  :from {:msg "No such variable in type environment", :term bool}}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] □))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] □),
           :from {:msg "Kind has not type" :term □}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] ✳))
 => '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
           :term (λ [x ✳] ✳), :codomain □,
           :from {:msg "Cannot calculate codomain type of product.", :term □,
                  :from {:msg "Kind has not type", :term □}}}])
(example
 (type-of-term {} '[[w ✳] [y w] [z y]] '(λ [x ✳] z))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] z),
           :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}])

;;{
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app [def-env env rator rand]
  (let [[status trator] (type-of-term def-env env rator)]
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
 (type-of-term {} '[[bool ✳] [y bool]]
          '[(λ [x bool] x) y])
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

(defn type-of-ref [def-env env name args]
  ;;(println "[type-of-ref] def-env=" def-env "env=" env "name=" name "args=" args)
  (let [[status ddef] (defenv/fetch-definition def-env name)]
    (cond
      (= status :ko) [:ko ddef]
      (not (defenv/latte-definition? ddef))
      (throw (ex-info "Not a LaTTe definition (please report)." {:def ddef}))
      (> (count args) (:arity ddef))
      [:ko {:msg "Too many arguments for definition." :term (list* name args) :arity ddef}]
      :else
      (loop [args args, params (:params ddef), sub {}]
        ;; (println "args=" args "params=" params "sub=" sub)
        (if (seq args)
          (let [arg (first args)
                ty (stx/subst (second (first params)) sub)]
            ;; (println "arg=" arg "ty=" ty)
            (if (not (type-check? def-env env arg ty))
              [:ko {:msg "Wrong argument type"
                    :term (list* name args)
                    :arg arg
                    :expected-type ty}]
              (recur (rest args) (rest params) (assoc sub (ffirst params) arg))))
          ;; all args have been checked
          (loop [params (reverse params), res (:type ddef)]
            (if (seq params)
              (recur (rest params) (list 'Π (first params) res))
              ;; all params have been handled
              (do
                ;; (println "[type-of-ref] res = " res " sub = " sub)
                [:ok (stx/subst res sub)]))))))))

(example
 (type-of-term {'test (defenv/map->Definition
                        '{:params [[x ✳] [y ✳]]
                          :type ✳
                          :arity 2})}
          '[[a ✳] [b ✳]]
          '(test a b))
 => '[:ok ✳])

(example
 (type-of-term {'test (defenv/map->Definition
                        '{:params [[x ✳] [y ✳]]
                          :type ✳
                          :arity 2})}
          '[[bool ✳] [a ✳] [b bool]]
          '(test a b))
 => '[:ko {:msg "Wrong argument type", :term (test b), :arg b, :expected-type ✳}])

(defn type-of
  ([t] (type-of {} [] t))
  ([env t] (type-of {} env t))
  ([def-env env t]
   (let [[status ty] (type-of-term def-env env t)]
     (if (= status :ko)
       (throw (ex-info "Type checking error" ty))
       ty))))

(defn proper-type?
  ([t] (proper-type? {} [] t))
  ([ctx t] (proper-type? {} ctx t))
  ([def-env ctx t]
   (let [ty (type-of def-env ctx t)]
     (let [sort (norm/beta-delta-normalize def-env ty)]
       (stx/sort? sort)))))
