(ns latte.kernel.defs
  "Handling definitions."

  (:require [latte.kernel.utils :as u])
  (:require [latte.kernel.presyntax :as stx])
  (:require [latte.kernel.typing :as ty])
  )

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

;;{
;; ## Theorem definitions
;;}

(defn handle-axiom-declaration [tdef def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (stx/parse def-env ty)]) params)
        ty (stx/parse def-env ty)]
    ;; (println "[handle-axiom-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env params ty))
      (throw (ex-info "Axiom is not a proper type" {:theorem (:name tdef) :type ty})))
    (assoc tdef
           :params params
           :arity (count params)
           :type ty)))

