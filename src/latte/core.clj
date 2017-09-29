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
       (or explanation "")))

;; example:
;; (definition id [[A :type]] (lambda [x A] x))


;;{
;; ## Theorems and lemmas
;;
;; The specs are as follows.
;;}

(s/def ::theorem (s/cat :name ::def-name
                        :doc (s/? ::def-doc)
                        :params ::def-params
                        :body ::def-body))

(declare handle-defthm)
(declare handle-thm-declaration)

(defmacro defthm
  "Declaration of a theorem of the specified `name` (first argument)
  an optional `docstring` (second argument), a vector of `parameters`
 and the theorem proposition (last argument).
 Each parameter is a pair `[x T]` with `x` the parameter name and `T` its
  type. 

  A theorem declared must later on be demonstrated using the [[proof]] form."
  [& args]
  (let [conf-form (s/conform ::theorem args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot declare theorem: syntax error."
                      {:explain (s/explain-str ::theorem args)}))
      (let [{thm-name :name doc :doc params :params body :body} conf-form]
        (let [[status def-name definition metadata] (handle-defthm :theorem thm-name doc params body)]
          (if (= status :ko)
            (throw (ex-info "Cannot declare theorem." {:name thm-name :error def-name}))
            `(do
               (def ~def-name ~definition)
               (alter-meta! (var ~def-name) #(merge % (quote ~metadata))) 
               [:declared :theorem (quote ~def-name)])))))))

(defmacro deflemma
  "Declaration of a lemma, i.e. an auxiliary theorem. In LaTTe a lemma
  is private. To export a theorem the [[defthm]] form must be used instead."
  [& args]
  (let [conf-form (s/conform ::theorem args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot declare lemma: syntax error."
                      {:explain (s/explain-str ::theorem args)}))
      (let [{thm-name :name doc :doc params :params body :body} conf-form]
        (let [[status def-name definition metadata] (handle-defthm :lemma thm-name doc params body)]
          (if (= status :ko)
            (throw (ex-info "Cannot declare lemma." {:name thm-name :error def-name}))
            `(do
               (def ~def-name ~definition)
               (alter-meta! (var ~def-name) #(merge % (quote ~metadata))) 
               [:declared :lemma (quote ~def-name)])))))))

(defn handle-defthm [kind thm-name doc params ty]
  (when (defenv/registered-definition? thm-name)
    (println "[Warning] redefinition as" (if (= kind :theorem)
                                           "theorem"
                                           "lemma") ":" thm-name))
  (let [[status definition] (handle-thm-declaration thm-name params ty)]
    (if (= status :ko)
      [:ko definition nil nil nil]
      (let [metadata {:doc (mk-doc (if (= kind :theorem)
                                     "Theorem"
                                     "Lemma") ty doc)
                      :arglists (list params)
                      :private (= kind :lemma)}]
        [:ok thm-name definition metadata]))))

(defn handle-thm-declaration [thm-name params ty]
  (let [[status params] (reduce (fn [[_ params] [x ty]]
                                  (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
                                    (if (= status :ko)
                                      (reduced [:ko ty'])
                                      [:ok (conj params [x ty'])]))) [:ok []] params)]
    (if (= status :ko)
      [:ko params]
      (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
        (if (= status :ko)
          [:ko ty']          
          (if (not (ty/proper-type? defenv/empty-env params ty'))
            [:ko {:msg "Theorem body is not a proper type" :theorem thm-name :type ty'}]
            [:ok (defenv/->Theorem thm-name params (count params) ty' false)]))))))



