(ns latte.kernel.typing
  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.utils :as u]
            [latte.kernel.syntax :as stx]
            [latte.kernel.norm :as norm]
            [latte.kernel.defenv :as defenv]))
  
(def ^:private +examples-enabled+)

;;{
;; # Type checking
;;}

;;{
;; ## Type context
;;}

(defn ctx-fetch [ctx x]
  ;; (println "[ctx-fetch] ctx=" ctx "x=" x)
  (if (seq ctx)
    (if (= (first (first ctx)) x)
      (second (first ctx))
      (recur (rest ctx) x))
    nil))

(defn ctx-put [ctx x t]
  (cons [x t] ctx))

(defn mk-ctx [& args]
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

(defn type-of-term [def-env ctx t]
  (let [[status ty]
        (cond
          (stx/kind? t) [:ko {:msg "Kind has not type" :term t}]
          (stx/type? t) (type-of-type)
          (stx/variable? t) (type-of-var def-env ctx t)
          ;; binders (lambda, prod)
          (stx/binder? t)
          (let [[binder [x ty] body] t]
            (case binder
              λ (type-of-abs def-env ctx x ty body)
              Π (type-of-prod def-env ctx x ty body)
              (throw (ex-info "No such binder (please report)" {:term t :binder binder}))))
          ;; references
          (stx/ref? t) (type-of-ref def-env ctx (first t) (rest t))
          ;; applications
          (stx/app? t) (type-of-app def-env ctx (first t) (second t))
          :else
          (throw (ex-info "Invalid term (please report)" {:term t})))]
    ;;(println "--------------------")
    ;;(println "[type-of-term] t=" t)
    ;;(clojure.pprint/pprint ty)
    ;;(println "--------------------")
    [status ty]))

(example
 (type-of-term {} [] '□) => '[:ko {:msg "Kind has not type" :term □}])

(defn type-check? [def-env ctx term type]
  ;;(println "[type-check?] term=" term "type=" type)
  ;;(println "    ctx=" ctx)
  (let [[status type'] (type-of-term def-env ctx term)]
    ;;(println "  ==> " status "type'=" type' "vs. type=" type)
    (if (= status :ok)
      (norm/beta-eq? def-env ctx type type')
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

(defn type-of-var [def-env ctx x]
  (if-let [ty (ctx-fetch ctx x)]
    (let [[status sort] (let [ty' (norm/normalize def-env ctx ty)]
                          (if (stx/kind? ty')
                            [:ok ty']
                            (type-of-term def-env ctx ty)))]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort}]
        (if (stx/sort? sort)
          [:ok ty]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x :type ty :sort sort}])))
    [:ko {:msg "No such variable in type context" :term x}]))

(example
 (type-of-term {} '[[bool ✳] [x bool]] 'x) => '[:ok bool])

(example
 (type-of-term {} '[[x bool]] 'x)
 => '[:ko {:msg "Cannot calculate type of variable.",
           :term x,
           :from {:msg "No such variable in type context", :term bool}}])

(example
 (type-of-term {} '[[y x] [x bool]] 'y)
 => '[:ko {:msg "Cannot calculate type of variable.", :term y, :from {:msg "Cannot calculate type of variable.", :term x, :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} '[[x ✳]] 'x)
 => '[:ok ✳])

(example
 (type-of-term {} '[[x □]] 'x)
 => '[:ok □])

(example
 (type-of-term {} '[[bool ✳] [y bool]] 'x)
 => '[:ko {:msg "No such variable in type context", :term x}])

;;{
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod [def-env ctx x A B]
  (let [[status sort1] (type-of-term def-env ctx A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term A :from sort1}]
      (let [sort1' (norm/normalize def-env ctx sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)" :term A :type sort1}]
          (let [ctx' (ctx-put ctx x A)
                [status sort2] (type-of-term def-env ctx' B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product." :term B :from sort2}]
              (let [sort2' (norm/normalize def-env ctx sort2)]
                ;; (println "sort2' = " sort2' " sort? " (stx/sort? sort2'))
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (not a sort)" :term B :type sort2}]
                  [:ok sort2])))))))))

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

(defn type-of-abs [def-env ctx x A t]
  (let [ctx' (ctx-put ctx x A)
        [status B] (type-of-term def-env ctx' t)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate codomain type of abstraction."
            :term (list 'λ [x A] t) :from B}]
      (let [tprod (list 'Π [x A] B)
            [status sort] (type-of-term def-env ctx tprod)]
        (if (= status :ko)
          [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                :term (list 'λ [x A] t)
                :codomain B :from sort}]
          (if (not (stx/sort? (norm/normalize def-env ctx sort)))
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
                  :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} '[[y ✳] [z y]] '(λ [x z] x))

 
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x z] x),
           :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}])

(example
 (type-of-term {} '[[y bool]] '(λ [x ✳] y))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] y),
           :from {:msg "Cannot calculate type of variable.", :term y,
                  :from {:msg "No such variable in type context", :term bool}}}])

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

(defn type-of-app [def-env ctx rator rand]
  (let [[status trator] (type-of-term def-env ctx rator)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate operator (left-hand) type in application."
            :term [rator rand] :from trator}]
      (let [trator' (norm/normalize def-env ctx trator)]
        (if (not (stx/prod? trator'))
          [:ko {:msg "Not a product type for operator (left-hand) in application." :term [rator rand] :operator-type trator}]
          (let [[_ [x A] B] trator']
            ;; (println "[type-of-app] trator'=" trator')
            (if (not (type-check? def-env ctx rand A))
              [:ko {:msg "Cannot apply: type domain mismatch" :term [rator rand] :domain A :operand rand}]
              (do ;;(println "[type-of-app] subst...")
                  ;;(println "    B = " B)
                  ;;(println "    x = " x)
                  ;;(println "    rand = " rand)
                  (let [res (stx/subst B x rand)]
                    ;;(println "   ===> " res)
                    [:ok res])))))))))


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

(defn type-of-ref [def-env ctx name args]
  (let [[status ty]
        (let [[status ddef] (defenv/fetch-definition def-env name)]
          (cond
            (= status :ko) [:ko ddef]
            (not (defenv/latte-definition? ddef))
            (throw (ex-info "Not a LaTTe definition (please report)." {:def ddef}))
            (defenv/special? ddef)
            (throw (ex-info "Special should not occur at typing time (please report)"
                            {:special ddef :term (list* name args)}))
            (defenv/notation? ddef)
            (throw (ex-info "Notation should not occur at typing time (please report)"
                            {:notation ddef :term (list* name args)}))
            (and (defenv/theorem? ddef)
                 (= (:proof ddef) false))
            [:ko {:msg "Theorem has no proof." :thm-name (:name ddef)}]
            (> (count args) (:arity ddef))
            [:ko {:msg "Too many arguments for definition." :term (list* name args) :arity (:arity ddef)}]
            :else
            (loop [args args, params (:params ddef), sub {}]
              ;; (println "args=" args "params=" params "sub=" sub)
              (if (seq args)
                (let [arg (first args)
                      ty (stx/subst (second (first params)) sub)]
                  ;; (println "arg=" arg "ty=" ty)
                  (if (not (type-check? def-env ctx arg ty))
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
                      ;;(println "[type-of-ref] res = " res " sub = " sub)
                      [:ok (stx/subst res sub)])))))))]
    ;;(println "---------------------")
    ;;(println "[type-of-ref] name=" name "args=" args)
    ;;(clojure.pprint/pprint ty)
    ;;(println "---------------------")
    [status ty]))

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
  ([ctx t] (type-of {} ctx t))
  ([def-env ctx t] (type-of-term def-env ctx t)))

(defn proper-type?
  ([t] (proper-type? {} [] t))
  ([ctx t] (proper-type? {} ctx t))
  ([def-env ctx t]
   (let [[status ty] (type-of def-env ctx t)]
     (if (= status :ko)
       (throw (ex-info "Type checking error" ty))
       (let [sort (norm/normalize def-env ctx ty)]
         (stx/sort? sort))))))
