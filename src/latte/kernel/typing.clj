(ns latte.kernel.typing
  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.utils :as u]
            [latte.kernel.presyntax :as parser]
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
  (get ctx x))

(defn ctx-put [ctx x t]
  (assoc ctx x t))

;;{
;; ## Synthesis rules
;;}

(declare type-of-type
         type-of-fvar
         type-of-bvar
         type-of-prod
         type-of-lambda
         type-of-app
         type-of-ref)

(defn type-of-term
  ([def-env ctx t] (type-of-term def-env ctx [] t))
  ([def-env ctx benv t]
   ;;(println "[type-of-term] benv=" benv)
   (let [[status ty]
         (cond
           (stx/kind? t) [:ko {:msg "Kind has not type" :term (stx/unparse t)}]
           (stx/type? t) (type-of-type)
           (stx/fvar? t) (type-of-fvar def-env ctx benv (:name t))
           (stx/bvar? t) (type-of-bvar def-env ctx benv (:index t))
           ;; binders (lambda, prod)
           (stx/binder? t)
           (case (stx/binder-kind t)
             :lambda (type-of-lambda def-env ctx benv (:name t) (:type t) (:body t))
             :prod (type-of-prod def-env ctx benv (:name t) (:type t) (:body t))
             (throw (ex-info "No such binder (please report)" {:term (stx/unparse t) :binder (stx/binder-kind t)})))
           ;; references
           (stx/ref? t) (type-of-ref def-env ctx benv (:name t) (:args t))
           ;; applications
           (stx/app? t) (type-of-app def-env ctx benv (:left t) (:right t))
           :else
           (throw (ex-info "Invalid term (please report)" {:term (stx/unparse t)})))]
     ;;(println "--------------------")
     ;;(println "[type-of-term] t=" t)
     ;;(clojure.pprint/pprint ty)
     ;;(println "--------------------")
     [status ty])))

(example
 (type-of-term {} {} '□) => '[:ko {:msg "Kind has not type" :term □}])

(defn type-check?
  ([def-env ctx term type] (type-check? ctx [] term type))
  ([def-env ctx benv term type]
   ;;(println "[type-check?] term=" term "type=" type)
   ;;(println "    ctx=" ctx)
   (let [[status type'] (type-of-term def-env ctx benv term)]
     ;;(println "  ==> " status "type'=" type' "vs. type=" type)
     (if (= status :ok)
       (norm/beta-eq? def-env ctx type type')
       (throw (ex-info "Cannot check type of term" {:term (stx/unparse term) :from type'}))))))

;;{
;;
;;     --------------------
;;     E |- Type ::> Kind
;;}

(defn type-of-type []
  [:ok '□])

(example
 (type-of-term {} {} '✳) => '[:ok □])

;;{
;;        ty::>Type or t::>Kind in E
;;     ------------------------------
;;        E,x::ty |- x ::> ty
;;}

(defn type-of-fvar [def-env ctx benv x]
  (if-let [ty (ctx-fetch ctx x)]
    (let [[status sort] (let [ty' (norm/normalize def-env ctx ty)]
                          (if (stx/kind? ty')
                            [:ok ty']
                            (type-of-term def-env ctx benv ty)))]
      (if (= status :ko)
        [:ko {:msg "Cannot calculate type of variable." :term x :from sort}]
        (if (stx/sort? sort)
          [:ok ty]
          [:ko {:msg "Not a correct type (super-type is not a sort)" :term x
                :type (stx/unparse ty) :sort (stx/unparse sort)}])))
    [:ko {:msg "No such variable in type context" :term x}]))

(example
 (type-of-term {} {'bool '✳
                    'x (stx/mk-fvar 'bool)}
               (stx/mk-fvar 'x))
 => '[:ok #latte.kernel.syntax.FVar{:name bool}])

(example
 (type-of-term {} {'x (stx/mk-fvar 'bool)} (stx/mk-fvar 'x))
 => '[:ko {:msg "Cannot calculate type of variable.",
           :term x,
           :from {:msg "No such variable in type context", :term bool}}])

(example
 (type-of-term {} {'y (stx/mk-fvar 'x)
                   'x (stx/mk-fvar 'bool)} (stx/mk-fvar 'y))
 => '[:ko {:msg "Cannot calculate type of variable.", :term y, :from {:msg "Cannot calculate type of variable.", :term x, :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} {'x '✳} (stx/mk-fvar 'x))
 => '[:ok ✳])

(example
 (type-of-term {} {'x '□} (stx/mk-fvar 'x))
 => '[:ok □])

(example
 (type-of-term {} {'bool '✳
                   'y (stx/mk-fvar 'bool)}
               (stx/mk-fvar 'x))
 => '[:ko {:msg "No such variable in type context", :term x}])


(defn type-of-bvar [def-env ctx benv index]
  (let [bindex (- (count benv) (inc index))]
    (if-let [ty (nth benv bindex)]
      (do
        (println "[type-of-bvar] index=" index "type=" (stx/unparse ty))
        (let [[status sort] (let [ty' (norm/normalize def-env ctx ty)]
                              (if (stx/kind? ty')
                                [:ok ty']
                                (type-of-term def-env ctx (into [] (take bindex benv)) ty)))]
          (do
            (println "  => sort of type=" sort)
            (if (= status :ko)
              [:ko {:msg "Cannot calculate type of bound variable." :index index :from sort}]
              (if (stx/sort? sort)
                [:ok ty]
                [:ko {:msg "Not a correct type (super-type is not a sort)" :term (keyword (str index))
                      :type (stx/unparse ty) :sort (stx/unparse sort)}])))))
      (throw (ex-info "No such bound variable (please report)"
                      {:index index})))))

(example
 (type-of-term {} '{bool ✳} [(stx/mk-fvar 'bool)]
               (stx/mk-bvar 0))
 => '[:ok #latte.kernel.syntax.FVar{:name bool}])

(example
 (type-of-term {} '{bool ✳} [(stx/mk-fvar 'bool) '✳]
               (stx/mk-bvar 0))
 => '[:ok ✳])

(example
 (type-of-term {} '{bool ✳} [(stx/mk-fvar 'bool) '✳]
               (stx/mk-bvar 1))
 => [:ok #latte.kernel.syntax.FVar{:name bool}])

(example
 (type-of-term {} {'x (stx/mk-fvar 'bool)} [(stx/mk-fvar 'x)] (stx/mk-bvar 0))
 => '[:ko {:msg "Cannot calculate type of bound variable.", :index 0,
           :from {:msg "Cannot calculate type of variable.", :term x,
                  :from {:msg "No such variable in type context", :term bool}}}])

;;{
;;    E |- A ::> s1     E,x:A |- B ::> s2
;;    -----------------------------------
;;     E |- prod x:A . B  ::>  s2
;;}

(defn type-of-prod [def-env ctx benv x A B]
  ;; (println "[type-of-prod] benv=" benv)
  (let [[status sort1] (type-of-term def-env ctx benv A)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate domain type of product." :term (stx/unparse A) :from sort1}]
      (let [sort1' (norm/normalize def-env ctx sort1)]
        (if (not (stx/sort? sort1'))
          [:ko {:msg "Not a valid domain type in product (super-type not a sort)"
                :term (stx/unparse A) :type (stx/unparse sort1)}]
          (let [[status sort2] (type-of-term def-env ctx (conj benv A) B)]
            (if (= status :ko)
              [:ko {:msg "Cannot calculate codomain type of product."
                    :term (stx/unparse B) :from sort2}]
              (let [sort2' (norm/normalize def-env ctx sort2)]
                ;; (println "sort2' = " sort2' " sort? " (stx/sort? sort2'))
                (if (not (stx/sort? sort2'))
                  [:ko {:msg "Not a valid codomain type in product (not a sort)"
                        :term (stx/unparse B) :type (stx/unparse sort2)}]
                  [:ok sort2])))))))))

(example
 (type-of-term {} {} (parser/parse '(Π [x ✳] x))) => '[:ok ✳])

(example
 (type-of-term {} {} (parser/parse '(Π [x ✳] ✳))) => '[:ok □])

(example
 (type-of-term {} {} (parser/parse '(Π [x □] ✳)))
 => '[:ko {:msg "Cannot calculate domain type of product.", :term □,
           :from {:msg "Kind has not type" :term □}}])

(example
 (type-of-term {} {} (parser/parse '(Π [x ✳] □)))
 => '[:ko {:msg "Cannot calculate codomain type of product.", :term □,
           :from {:msg "Kind has not type" :term □}}])


;;{
;;    E,x:A |- t ::> B  E |- prod x:A. B ::> s
;;    --------------------------------------------
;;    E |- lambda x:A . t  ::>  prod x:A . B
;;}

(defn type-of-lambda [def-env ctx benv x A t]
  (println "[type-of-lambda] x=" x "A=" (stx/unparse A) "t=" (stx/unparse t))
  (println "  ==> benv=" (map stx/unparse benv))
  (let [[status B] (type-of-term def-env ctx (conj benv A) t)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate codomain type of abstraction."
            :term (stx/unparse (stx/mk-lambda x A t)) :from B}]
      (do (println "  ==> B=" (stx/unparse B))
          (let [tprod (stx/mk-prod x A (stx/close B x))
                _ (println "  ==> tprod=" (stx/unparse tprod))
                [status sort] (type-of-term def-env ctx benv tprod)]
            (do (println "  ==> sort=" (stx/unparse sort))
                (if (= status :ko)
                  [:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type)."
                        :term (stx/unparse (stx/mk-lambda x A t))
                        :codomain B :from sort}]
                  (if (not (stx/sort? (norm/normalize def-env ctx sort)))
                    [:ko {:msg "Not a valid codomain type in abstraction (super-type not a sort)."
                          :term (stx/unparse (stx/mk-lambda x A t))
                          :codomain (stx/unparse B)
                          :type (stx/unparse sort)}]
                    (do
                      (println "  ==> type-of-lambda=" (stx/unparse tprod))
                      [:ok tprod])))))))))

(example
 (stx/unparse
  (second
   (type-of-term {} {'bool '✳
                     't (stx/mk-fvar 'bool)
                     'y (stx/mk-fvar 'bool)}
                 (parser/parse '(λ [x bool] x)))))
 => '(Π [x bool] bool))

(example
 (stx/unparse
  (second
   (type-of-term {} {} (parser/parse '(λ [x ✳] x)))))
 => '(Π [x ✳] ✳))

(example
 (type-of-term {} {'y (stx/mk-fvar 'bool)} (parser/parse '(λ [x bool] x)))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x bool] x),
           :from {:msg "Cannot calculate type of bound variable.", :index 0,
                  :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} {'y '✳
                   'z (stx/mk-fvar 'y)} (parser/parse '(λ [x z] x)))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x z] x),
           :from {:msg "Not a correct type (super-type is not a sort)", :term :0, :type z, :sort y}}])

(example
 (type-of-term {} {'y (stx/mk-fvar 'bool)} (parser/parse '(λ [x ✳] y)))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] y),
           :from {:msg "Cannot calculate type of variable.", :term y,
                  :from {:msg "No such variable in type context", :term bool}}}])

(example
 (type-of-term {} {} (parser/parse '(λ [x ✳] □)))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] □),
           :from {:msg "Kind has not type" :term □}}])

(example
 (type-of-term {} {} (parser/parse '(λ [x ✳] ✳)))
 => '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
           :term (λ [x ✳] ✳), :codomain □,
           :from {:msg "Cannot calculate codomain type of product.", :term □,
                  :from {:msg "Kind has not type", :term □}}}])
(example
 (type-of-term {} {'w '✳, 'y (stx/mk-fvar 'w), 'z (stx/mk-fvar 'y)}
               (parser/parse '(λ [x ✳] z)))
 => '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] z),
           :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}])



;;{
;;       E |- rator ::> prod x:A . B    E|- rand :: A
;;    -------------------------------------------------
;;          E |- rator rand : B [rand/x]
;;}

(defn type-of-app [def-env ctx benv rator rand]
  (let [[status trator] (type-of-term def-env ctx benv rator)]
    (if (= status :ko)
      [:ko {:msg "Cannot calculate operator (left-hand) type in application."
            :term (stx/unparse (stx/mk-app rator rand)) :from trator}]
      (let [trator' (norm/normalize def-env ctx trator)]
        (if (not (stx/prod? trator'))
          [:ko {:msg "Not a product type for operator (left-hand) in application." :term (stx/unparse (stx/mk-app rator rand)) :operator-type (stx/unparse trator)}]
          (if (not (type-check? def-env ctx benv rand (:type trator')))
            [:ko {:msg "Cannot apply: type domain mismatch" :term (stx/unparse (stx/mk-app rator rand)) :domain (stx/unparse (:type trator')) :operand (stx/unparse rand)}]
            (do (println "[type-of-app] subst...")
                (println "    body trator' = " (stx/unparse (:body trator')))
                (println "    rand = " (stx/unparse rand))
              (let [res (stx/apply-to (:body trator') rand)]
                (println "   ===> " (stx/unparse res))
                [:ok res]))))))))

(example
 (type-of-term {} {'bool '✳, 'y (stx/mk-fvar 'bool)}
               (parser/parse '[(λ [x bool] x) y]))
 => '[:ok #latte.kernel.syntax.FVar{:name bool}])

;;{
;;    D |- ref :: [x1 t1] [x2 t2] ... [xN tN] -> t
;;    E |- e1 :: t1   E, x1:t1 |- e2 :: t2
;;    ...
;;    E, x1:t1, ..., xM-1:tM-1 |- eM :: tM
;; -------------------------------------------------------------------------------------
;;      D, E |- (ref e1 e2 ... eM)
;;              ::> (prod [xM+1 tM+1] ... (prod [xN tN] t [e1/x1, e2/x2, ...eM/xM]) ...)
;;}

(defn type-of-ref [def-env ctx benv name args]
  (let [[status ty]
        (let [[status ddef] (defenv/fetch-definition def-env name)]
          (cond
            (= status :ko) [:ko ddef]
            (not (defenv/latte-definition? ddef))
            (throw (ex-info "Not a LaTTe definition (please report)." {:def ddef}))
            (defenv/special? ddef)
            (throw (ex-info "Special should not occur at typing time (please report)"
                            {:special ddef :term (stx/unparse (stx/mk-ref name args))}))
            (defenv/notation? ddef)
            (throw (ex-info "Notation should not occur at typing time (please report)"
                            {:notation ddef :term (stx/unparse (stx/mk-ref name args))}))
            (and (defenv/theorem? ddef)
                 (= (:proof ddef) false))
            [:ko {:msg "Theorem has no proof." :thm-name (:name ddef)}]
            (> (count args) (:arity ddef))
            [:ko {:msg "Too many arguments for definition." :term (stx/unparse (stx/mk-ref name args)) :arity (:arity ddef)}]
            :else
            (loop [args args, params (:params ddef), sub {}]
              ;; (println "args=" args "params=" params "sub=" sub)
              (if (seq args)
                (let [arg (first args)
                      ty (stx/subst (second (first params)) sub)]
                  ;; (println "arg=" arg "ty=" ty)
                  (if (not (type-check? def-env ctx benv arg ty))
                    [:ko {:msg "Wrong argument type"
                          :term (stx/unparse (stx/mk-ref name args))
                          :arg (stx/unparse arg)
                          :expected-type (stx/unparse ty)}]
                    (recur (rest args) (rest params) (assoc sub (ffirst params) arg))))
                ;; all args have been checked
                (loop [params (reverse params), res (stx/subst (:type ddef) sub)]
                  (if (seq params)
                    (recur (rest params) (stx/mk-prod (ffirst params) (second (first params))
                                                      (stx/close res (ffirst params))))
                    ;; all params have been handled
                    (do
                      ;;(println "[type-of-ref] res = " res " sub = " sub)
                      [:ok res])))))))]
    ;;(println "---------------------")
    ;;(println "[type-of-ref] name=" name "args=" args)
    ;;(clojure.pprint/pprint ty)
    ;;(println "---------------------")
    [status ty]))

(example
 (let [def-env {'test (defenv/map->Definition
                          '{:params [[x ✳] [y ✳]]
                            :type ✳
                            :arity 2})}]
   (type-of-term def-env
                 '{a ✳, b ✳}
                 (parser/parse def-env '(test a b))))
 => '[:ok ✳])

(example
 (let [def-env {'test (defenv/map->Definition
                        '{:params [[x ✳] [y ✳]]
                          :type ✳
                          :arity 2})}]
   (type-of-term def-env
    {'bool '✳, 'a '✳, 'b (stx/mk-fvar 'bool)}
    (parser/parse def-env '(test a b))))
 => '[:ko {:msg "Wrong argument type", :term (test b), :arg b, :expected-type ✳}])

(defn type-of
  ([t] (type-of {} [] t))
  ([ctx t] (type-of {} ctx t))
  ([def-env ctx t]
   (let [[status ty] (type-of-term def-env ctx t)]
     (if (= status :ko)
       (throw (ex-info "Type checking error" ty))
       ty))))

(defn proper-type?
  ([t] (proper-type? {} [] t))
  ([ctx t] (proper-type? {} ctx t))
  ([def-env ctx t]
   (let [ty (type-of def-env ctx t)]
     (let [sort (norm/normalize def-env ctx ty)]
       (stx/sort? sort)))))
