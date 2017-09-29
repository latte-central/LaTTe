(ns latte.core
  "This namespace provides the top-level forms of the LaTTe
  framework."

  (:require [clojure.spec.alpha :as s]
            [clojure.pprint :as pp]
            [latte-kernel.utils :as u]
            [latte-kernel.presyntax :as stx]
            [latte-kernel.typing :as ty]
            [latte-kernel.norm :as n]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :as p]))

;;{
;; ## Definitions
;;
;; We begin with a lightweight spec of definitions (for simple error checking).
;;}

(s/def ::def-name symbol?)
(s/def ::def-doc string?)
(s/def ::type-decl #(or (symbol? %)
                        (keyword? %)))
(s/def ::param (s/tuple symbol? ::type-decl))
(s/def ::def-params (s/coll-of ::param :kind vector?))
(s/def ::def-body any?)

(s/def ::definition (s/cat :name ::def-name
                           :doc (s/? ::def-doc)
                           :params ::def-params
                           :body ::def-body))


(declare handle-term-definition)
(declare mk-doc)

(defmacro definition
  "Defines a mathematical term composed of a `name`, and optional (but highly recommended)
  `docstring`, a vector of `parameters` and a `lambda-term` as definitional content.

  An `ex-info` exception is thrown if the term cannot be defined.

  Note that it is a Clojure `def`, the term is defined in the namespace where the `definition` 
  form is invoked."
  [& args]
  (let [conf-form (s/conform ::definition args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot define term: syntax error."
                      {:explain (s/explain-str ::definition args)}))
      (let [{def-name :name doc :doc params :params body :body} conf-form]
        (when (defenv/registered-definition? def-name)
          (println "[Warning] redefinition as term: " def-name))
        (let [[status definition] (handle-term-definition def-name params body)]
          (when (= status :ko)
            (throw (ex-info "Cannot define term." {:name def-name, :error definition})))
          (let [quoted-def# definition]
            `(do
               (def ~def-name ~quoted-def#)
               (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                             :doc (mk-doc "Definition" (quote ~body) ~doc)
                                                             :arglists (list (quote ~params)))))
               [:defined :term (quote ~def-name)])))))))

(defn handle-term-definition [def-name params body]
  ;; parse parameters
  (let [[status params] (reduce (fn [[sts params] [x ty]]
                                  (let [[status ty] (stx/parse-term defenv/empty-env ty)]
                                    (if (= status :ko)
                                      (reduced [:ko ty])
                                      [:ok (conj params [x ty])]))) [:ok []] params)]
    (if (= status :ko)
      [:ko params]
      (let [[status body-term] (stx/parse-term defenv/empty-env body)]
        (if (= status :ko)
          [:ko body-term]
          (let [[status ty] (ty/type-of-term defenv/empty-env params body-term)]
            (if (= status :ko)
              [:ko ty]
              [:ok (defenv/->Definition def-name params (count params) body-term ty)])))))))

(defn mk-doc [kind content explanation]
  (str "\n```\n"
       (with-out-str
         (pp/pprint content))
       "```\n**" kind "**: "
       explanation))

;; example:
;; (definition id [[A :type]] (lambda [x A] x))



