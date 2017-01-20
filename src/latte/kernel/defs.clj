
(ns latte.kernel.defs
  "Handling definitions."

  (:require [latte.kernel.utils :as u]
            [latte.kernel.presyntax :as parser]
            [latte.kernel.syntax :as stx]
            [latte.kernel.defenv :refer [->Definition ->Theorem ->Axiom]]
            [latte.kernel.typing :as ty]
            [latte.kernel.norm :as n]))

;;{
;; ## Term definitions
;;}

(defn handle-term-definition [def-name def-env ctx params body def-type]
  (let [[status params] (reduce (fn [[sts params] [x ty]]
                                  (let [[status ty] (parser/parse-term def-env ty)]
                                    (if (= status :ko)
                                      (reduced [:ko ty])
                                      [:ok (conj params [x ty])]))) [:ok []] params)]
    (if (= status :ko)
      [:ko params]
      (let [[status body] (parser/parse-term def-env body)]
        (if (= status :ko)
          [:ko body]
          (let [[status ty] (ty/type-of-term def-env (u/to-map (concat params ctx)) body)]
            (if (= status :ko)
              [:ko ty]
              (if def-type
                (let [[status def-ty] (parser/parse-term def-env def-type)]
                  (if (= status :ko)
                    [:ko def-ty]
                    (let [def-ty (loop [params params, def-ty def-ty]
                                   (if (seq params)
                                     (recur (rest params) (stx/mk-prod (ffirst params)
                                                                       (second (first params))
                                                                       (stx/close def-ty (ffirst params))))
                                     def-ty))]
                      (if (n/beta-eq? def-env ctx ty def-ty)
                        [:ok (->Definition def-name params (count params) body def-ty)]
                        [:ko {:msg "Definition type mismatch."
                              :def-name def-name
                              :computed-type (stx/unparse ty)
                              :def-type (stx/unparse def-ty)}]))))
                ;; use computed type
                [:ok (->Definition def-name params (count params) body ty)]))))))))

(defn handle-local-term-definition [def-name body def-type]
  [:ok (->Definition def-name [] 0 body def-type)])

(defn handle-local-term-discharge [local-def x ty]
  (let [{def-name :name parsed-term :parsed-term type :type} local-def]
    (->Definition def-name [] 0
                  (do
                    (println "discharge" def-name "with" x "->")
                    (print "  ==> [before] ")(clojure.pprint/pprint (stx/unparse parsed-term))
                    (print "  ==> [after] ")(clojure.pprint/pprint (stx/unparse (stx/mk-lambda x ty (stx/close parsed-term x))))
                    (stx/mk-lambda x ty (stx/close parsed-term x)))
                  (stx/mk-prod x ty (stx/close type x)))))

;;{
;; ## Theorem definitions
;;}

(defn handle-thm-declaration [thm-name def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (parser/parse def-env ty)]) params)
        ty (parser/parse def-env ty)]
    ;; (println "[handle-thm-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env (u/to-map params) ty))
      (throw (ex-info "Theorem is not a proper type" {:theorem thm-name :type (stx/unparse ty)})))
    (->Theorem thm-name params (count params) ty false)))

;;{
;; ## Axiom definitions
;;}

(defn handle-axiom-declaration [ax-name def-env params ty]
  (let [params (mapv (fn [[x ty]] [x (parser/parse def-env ty)]) params)
        ty (parser/parse def-env ty)]
    ;; (println "[handle-axiom-definition] def-env = " def-env " params = " params " body = " body)
    (when (not (ty/proper-type? def-env (u/to-map params) ty))
      (throw (ex-info "Axiom is not a proper type" {:theorem ax-name :type (stx/unparse ty)})))
    (->Axiom ax-name params (count params) ty)))


