(ns latte.defs
  (:require [latte.utils :as u])
  (:require [latte.presyntax :as stx])
  (:require [latte.typing :as ty])
  )

;;{
;; # Definitions
;;}


;;{
;; ## Definitional environment
;;}

(defn latte-definition? [v]
  (and (map? v)
       (contains? v :tag)
       (contains? #{:term :theorem :axiom} (:tag v))))

(defn build-initial-definition-environment!
  []
  (let [ns-env (ns-map *ns*)]
    ;; (if (contains? ns-env '+latte-definition-environment+)
    ;;   (throw (ex-info "Cannot build initial definition environment: already existing" {:namespace (namespace '+latte-definition-environment+)
    ;;                                                                                    :var '+latte-definition-environment+}))
    (intern (ns-name *ns*) '+latte-definition-environment+
            (atom (reduce (fn [def-env [name definition]]
                            ;; (print "name = " name "def = " definition)
                            (if (latte-definition? definition)
                              (do (print "name = " name "def = " definition)
                                  (println " (... latte definition registered ...)")
                                  (assoc def-env name definition))
                              (do ;; (println " (... not a latte definition ...)")
                                def-env))) {} ns-env)))))
;;)

(defn fetch-def-env-atom
  []
  (let [lvar (let [lv (resolve '+latte-definition-environment+)]
               (if (not lv)
                 (do (build-initial-definition-environment!)
                     (resolve '+latte-definition-environment+))
                 lv))]
    ;;(println "Resolved!" lvar)
    @lvar))


(defn fetch-definition-environment
  []
  @(fetch-def-env-atom))

(defn register-definition! [name definition]
   (let [def-atom (fetch-def-env-atom)]
     (swap! def-atom (fn [def-env]
                       (assoc def-env name definition)))))

;;{
;; ## Term definitions
;;}

(defn handle-term-definition [tdef def-env ctx params body]
  (let [[status params] (reduce (fn [[sts params] [x ty]]
                                  (let [[status ty] (stx/parse-term def-env ty)]
                                    (if (= status :ko)
                                      (reduced [:ko ty])
                                      [:ok (conj params [x ty])]))) [:ok []] params)]
    (if (= status :ko)
      [:ko params]
      (let [[status body] (stx/parse-term def-env body)]
        (if (= status :ko)
          [:ko body]
          (let [[status ty] (ty/type-of-term def-env (u/vconcat params ctx) body)]
            (if (= status :ko)
              [:ko ty]
              [:ok (assoc tdef
                          :params params
                          :arity (count params)
                          :type ty
                          :parsed-term body)])))))))

;;{
;; ## Theorem definitions
;;}

(defn handle-thm-declaration [tdef def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (stx/parse def-env ty)]) params)
        ty (stx/parse def-env ty)]
    ;; (println "[handle-thm-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env params ty))
      (throw (ex-info "Theorem is not a proper type" {:theorem (:name tdef) :type ty})))
    (assoc tdef
           :params params
           :arity (count params)
           :type ty
           :proof false)))
