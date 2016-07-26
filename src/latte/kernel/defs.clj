(ns latte.kernel.defs
  "Handling definitions."

  (:require [latte.kernel.utils :as u])
  (:require [latte.kernel.presyntax :as stx])
  (:require [latte.kernel.typing :as ty])
  )

;;{
;; ## Term definitions
;;}

(defrecord Definition [name params arity parsed-term type])

(defn definition? [v]
  (instance? Definition v))

(defn handle-term-definition [def-name def-env ctx params body]
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
              [:ok (->Definition def-name params (count params) body ty)])))))))

;;{
;; ## Theorem definitions
;;}

(defrecord Theorem [name params arity type proof])

(defn theorem? [v]
  (instance? Theorem v))

(defn handle-thm-declaration [thm-name def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (stx/parse def-env ty)]) params)
        ty (stx/parse def-env ty)]
    ;; (println "[handle-thm-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env params ty))
      (throw (ex-info "Theorem is not a proper type" {:theorem thm-name :type ty})))
    (->Theorem thm-name params (count params) ty false)))

;;{
;; ## Theorem definitions
;;}

(defrecord Axiom [name params arity type])

(defn axiom? [v]
  (instance? Axiom v))

(defn handle-axiom-declaration [ax-name def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (stx/parse def-env ty)]) params)
        ty (stx/parse def-env ty)]
    ;; (println "[handle-axiom-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env params ty))
      (throw (ex-info "Axiom is not a proper type" {:theorem ax-name :type ty})))
    (->Axiom ax-name params (count params) ty)))

(defn latte-definition? [v]
  (or (definition? v)
      (theorem? v)
      (axiom? v)))
