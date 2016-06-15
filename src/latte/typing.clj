(ns typetheory.typing
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [clojure.spec :as s])
  (:require [clojure.test.check :as tc])
  (:require [clojure.test.check.generators :as gen])
  (:require [clojure.test.check.properties :as prop])
  (:require [typetheory.syntax :as sx])
  (:require [typetheory.beta :as b])
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

;;{
;; ## Synthesis rules
;;}

(declare type-of-type
         type-of-var
         type-of-prod
         type-of-abs
         type-of-app)

(defn type-of [env term]
  (let [[tag _] (sx/validate ::sx/term term)]
    (case tag
      :kind [:ko {:msg "Kind has not type"}]
      :type (type-of-type)
      :var (type-of-var env term)
      :bind (let [[binder [x ty] body] term]
              (case binder
                lambda (type-of-abs env x ty body)
                prod (type-of-prod env x ty body)
                (throw (ex-info "No such binder (please report)" {:binder binder}))))
      :app (type-of-app env (first term) (second term))
      (throw (ex-info "Invalid term (please report)" {:term term})))))

(example
 (type-of [] :kind) => [:ko {:msg "Kind has not type"}])

(defn type-check? [env term type]
  (let [[status type'] (type-of env term)]
    (if (= status :ok)
      (b/beta-eq? type type')
      (throw (ex-info "Cannot check type of term" {:term term :env env})))))


;;{
;;
;;     --------------------
;;     E |- Type ::> Kind
;;}

(defn type-of-type []
  [:ok :kind])

(example
 (type-of [] :type) => [:ok :kind])

;;{
;;        ty::>Type or t::>Kind in E
;;     ------------------------------
;;        E,x::ty |- x ::> ty
;;}

(defn type-of-var [env x]
  (if-let [ty (env-fetch env x)]
    (let [[status sort :as res] (type-of env ty)]
      ;;(println "ty=" ty)
      ;;(println "res=" res)
      (if (= status :ok)
        (if (s/valid? ::sx/sort (b/normalize sort))
          [:ok ty]
          [:ko {:msg "Not a correct type" :term ty :env env}])
        res))
    [:ko {:msg "No such variable" :term x :env env}]))

(example
 (type-of '[[bool :type] [x bool]] 'x) => '[:ok bool])

(example
 (type-of '[[x bool]] 'x)
 => '[:ko {:msg "No such variable", :term bool, :env [[x bool]]}])

(example
 (type-of '[[bool :type] [y bool]] 'x)
 => '[:ko {:msg "No such variable", :term x, :env [[bool :type] [y bool]]}])


;;{
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod [env x A B]
  (let [[status sort1 :as res] (type-of env A)]
    (if (= status :ko)
      res
      (if (not (s/valid? ::sx/sort (b/normalize sort1)))
        [:ko {:msg "Not a valid type" :term A :env env}]
        (let [env' (env-put env x A)
              [status sort2 :as res] (type-of env' B)]
          (if (= status :ko)
            res
            (if (not (s/valid? ::sx/sort (b/normalize sort2)))
              [:ko {:msg "Not a valid type" :term B :env env'}]
              [:ok sort2])))))))

(example
 (type-of [] '(prod [x :type] x)) => [:ok :type])

(example
 (type-of [] '(prod [x :type] :type)) => [:ok :kind])

(example
 (type-of [] '(prod [x :kind] :type))
 => [:ko {:msg "Kind has not type"}])

(example
 (type-of [] '(prod [x :type] :kind))
 => [:ko {:msg "Kind has not type"}])

;;{
;;    E,x:A |- t ::> B  E |- prod x:A. B ::> s
;;    --------------------------------------------
;;    E |- lambda x:A . t  ::>  prod x:A . B
;;}

(defn type-of-abs [env x A t]
  (let [env' (env-put env x A)
        [status B :as res] (type-of env' t)]
    (if (= status :ko)
      res
      (let [tprod (list 'prod [x A] B)
            [status sort :as res] (type-of env tprod)]
        (if (= status :ko)
          res
          (if (not (s/valid? ::sx/sort (b/normalize sort)))
            [:ko {:msg "Not a valid type" :term tprod :env env}]
            [:ok tprod]))))))

(example
 (type-of '[[bool :type] [t bool] [y bool]]
          '(lambda [x bool] x))
 => '[:ok (prod [x bool] bool)])

(example
 (type-of [] '(lambda [x :type] x)) => '[:ok (prod [x :type] :type)])

(example
 (type-of '[[y bool]] '(lambda [x bool] x))
 => '[:ko {:msg "No such variable", :term bool, :env [[y bool] [x bool]]}])

 (example
  (type-of '[[y :type] [z y]] '(lambda [x z] x))
  => '[:ko {:msg "Not a correct type", :term z, :env [[y :type] [z y] [x z]]}])

(example
 (type-of '[[y bool]] '(lambda [x :type] y))
 => '[:ko {:msg "No such variable", :term bool, :env [[y bool] [x :type]]}])

(example
 (type-of '[[y bool]] '(lambda [x :type] :kind))
 => [:ko {:msg "Kind has not type"}])

(example
 (type-of '[[y bool]] '(lambda [x :type] :type))
 => [:ko {:msg "Kind has not type"}])

 (example
  (type-of '[[w :type] [y w] [z y]] '(lambda [x :type] z))
  => '[:ko {:msg "Not a correct type",
            :term y,
            :env [[w :type] [y w] [z y] [x :type]]}])

;;{
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app [env rator rand]
  (let [[status trator :as res] (type-of env rator)]
    (if (= status :ko)
      res
      (let [trator' (b/normalize trator)]
        (if (not (s/valid? ::sx/product trator'))
          [:ko {:msg "Not a product type" :term rator :type trator :env env}]
          (let [[_ [x A] B] trator']
            (if (not (type-check? env rand A))
              [:ko {:msg "Cannot apply" :dom A :operand rand}]
              [:ok (sx/subst B x rand)])))))))


(example
 (type-of '[[bool :type] [y bool]]
          '((lambda [x bool] x) y)) => '[:ok bool])

