(ns latte.core
  "This namespace provides the top-level forms of the LaTTe
  framework."

  (:require [clojure.spec.alpha :as s]
            [clojure.pprint :as pp]
            [latte-kernel.utils :as u]
            [latte-kernel.presyntax :as stx]
            [latte-kernel.unparser :as unparser]
            [latte-kernel.typing :as ty]
            [latte-kernel.norm :as n]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :as p]))

;; Initialisation of unparser
(unparser/install-fundamental-unparsers!)

;;{
;; ## Definitions
;;
;; We begin with a lightweight spec of definitions (for simple error checking).
;;}

(s/def ::def-name symbol?)
(s/def ::def-doc string?)
(s/def ::param (s/tuple symbol? any?))
(s/def ::def-params (s/coll-of ::param :kind vector?))
(s/def ::def-body any?)

(s/def ::definition (s/cat :name ::def-name
                           :doc (s/? ::def-doc)
                           :params ::def-params
                           :body ::def-body))


(declare handle-term-definition)
(declare mk-def-doc)

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
                                                             :doc (mk-def-doc "Definition" (quote ~body) ~doc)
                                                             :arglists (list (quote ~params)))))
               [:defined :term (quote ~def-name)])))))))

(defn parse-parameters [def-env params]
  (reduce (fn [[sts params] [x ty]]
            (let [[status ty] (stx/parse-term def-env ty)]
              (if (= status :ko)
                (reduced [:ko ty])
                [:ok (conj params [x ty])]))) [:ok []] params))

(defn handle-term-definition [def-name params body]
  ;; parse parameters
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      (let [[status body-term] (stx/parse-term defenv/empty-env body)]
        (if (= status :ko)
          [:ko body-term]
          (let [[status ty _] (ty/type-of-term defenv/empty-env params body-term)]
            (if (= status :ko)
              [:ko ty]
              [:ok (defenv/->Definition def-name params (count params) body-term ty {})])))))))

(defn mk-def-doc [kind content explanation]
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
      (let [metadata {:doc (mk-def-doc (if (= kind :theorem)
                                     "Theorem"
                                     "Lemma") ty doc)
                      :arglists (list params)
                      :private (= kind :lemma)}]
        [:ok thm-name definition metadata]))))

(defn handle-thm-declaration [thm-name params ty]
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
        (if (= status :ko)
          [:ko ty']          
          (if (not (ty/proper-type? defenv/empty-env params ty'))
            [:ko {:msg "Theorem body is not a proper type" :theorem thm-name :type ty'}]
            [:ok (defenv/->Theorem thm-name params (count params) ty' false)]))))))


;;{
;; ## Axioms
;;}

(s/def ::axiom (s/cat :name ::def-name
                      :doc (s/? ::def-doc)
                      :params ::def-params
                      :body ::def-body))

(declare handle-defaxiom)
(declare handle-ax-declaration)

(defmacro defaxiom
  "Declaration of an axiom with the specified `name` (first argument)
  an optional `docstring` (second argument), a vector of `parameters`
 and the axiom statement (last argument).
 Each parameter is a pair `[x T]` with `x` the parameter name and `T` its
  type. 

  An axiom is accepted without a proof, and should thus be used with
extra care. The LaTTe rule of thumb is that theorems should be
favored, but axioms are sometimes required (e.g. the law of the excluded
 middle) or more \"reasonable\" because of the proof length or complexity.
In all cases the introduction of an axiom must be justified with strong
 (albeit informal) arguments."
  [& args]
  (let [conf-form (s/conform ::axiom args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot declare axiom: syntax error."
                      {:explain (s/explain-str ::axiom args)}))
      (let [{ax-name :name doc :doc params :params body :body} conf-form]
        (let [[status def-name definition metadata] (handle-defaxiom :axiom ax-name doc params body)]
          (if (= status :ko)
            (throw (ex-info "Cannot declare axiom." {:name ax-name :error def-name}))
            `(do
               (def ~def-name ~definition)
               (alter-meta! (var ~def-name) #(merge % (quote ~metadata))) 
               [:declared :axiom (quote ~def-name)])))))))

(defn handle-defaxiom [kind ax-name doc params ty]
  (when (defenv/registered-definition? ax-name)
    (println "[Warning] redefinition as" (if (= kind :axiom)
                                           "axiom"
                                           "primitive") ":" ax-name))
  (let [[status definition] (handle-ax-declaration ax-name params ty)]
    (if (= status :ko)
      [:ko definition nil nil nil]
      (let [metadata {:doc (mk-def-doc (if (= kind :axiom)
                                     "Axiom"
                                     "Lemma") ty doc)
                      :arglists (list params)}]
        [:ok ax-name definition metadata]))))

(defn handle-ax-declaration [ax-name params ty]
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
        (if (= status :ko)
          [:ko ty']          
          (if (not (ty/proper-type? defenv/empty-env params ty'))
            [:ko {:msg "Axiom body is not a proper type" :axiom ax-name :type ty'}]
            [:ok (defenv/->Axiom ax-name params (count params) ty')]))))))

;;{
;; ## Proofs
;;
;; The specs are as follows.
;;}

(s/def ::assume (s/cat :command #(= % :assume)
                       :params ::def-params
                       :body any?
                       :meta (s/? map?)))

(s/def ::have (s/cat :command #(= % :have)
                     :have-type any?
                     :by-kw #(= % :by)
                     :have-term any?
                     :meta (s/? map?)))

(s/def ::qed (s/cat :command #(= % :qed)
                    :qed-term any?
                    :meta (s/? map?)))



(s/def ::have-args (s/cat :have-name symbol?
                          :have-type any?
                          :by-kw #(= % :by)
                          :have-term any?))

(defmacro have
  "A have step of the form `(have <x> T :by e)` checks that the
 term `e` is of type `T`. If it is the case, then the fact is recorded
 as a local definition named `<x>`. Otherwise an error is signaled.
The type `T` can be replaced by `_` in which case is is inferred rather than checked.
The name `<x>` can be replaced by `_` in which case no definition is recorded."
  [have-name have-type by-kw have-term]
  (let [infos (meta &form)
        conf-form (s/conform ::have-args (rest &form))]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Have step syntax error."
                      {:infos infos
                       :explain (s/explain-str ::have-args (rest &form))}))
      `[:have (quote ~have-name) (quote ~have-type) (quote ~have-term) ~(or infos {})])))

(defmacro pose
  "A local definition `(pose P := e)` allows a proof to refer to term `e` under
the name `P` in a proof. This is equivalent to `(have P _ :by e)` (with the type of
`e` inferred)."
  [pose-name pose-kw pose-term]
  `(have ~pose-name ~(symbol "_") :by ~pose-term))

(defmacro qed
  "A Qed step of the form `(qed e)` checks that the
 term `e` allows to finish a proof in the current context.
An error is signaled if the proof cannot be concluded."
  [qed-term]
  `[:qed (quote ~qed-term) ~(meta &form)])


(defmacro assume
  "An assume step of the form `(assume [x1 T1 x2 T2 ...] <body>)`.
"
  {:style/indent [1 :form [1]]}
  [params & body]
    `[:assume ~(meta &form) (quote ~params) 
        ~@body])



(defn proof
  "Provides a proof of theorem named `thm-name` using the given proof `method`
  and `steps`.
  There are for now two proof methods available:
    - the `:term` method with one step: a direct proof/lambda-term
      inhabiting the theorem/type (based on the proof-as-term, proposition-as-type
      correspondances). This is a low-level proof method. 

    - the `:script` method with a declarative proof script. It is a high-level
  (human-readable) proof method. A low-level proof term is
  synthetized from the script"
  {:style/indent [2 :form :form [1]]}
  [thm-name method & steps]
  (let [def-env defenv/empty-env
        [status thm] (if (symbol? thm-name)
                       (let [[status', thm] (defenv/fetch-definition def-env thm-name)]
                         (if (= status' :ko)
                           [:ko {:msg "No such theorem." :name thm-name}]
                           (if (not (defenv/theorem? thm))
                             [:ko {:msg "Not a theorem." :name thm-name, :value thm}]
                             [:ok thm])))
                       [:ko {:msg "Not a theorem name."
                             :thm-name thm-name}])]
    (when (= status :ko)
      (throw (ex-info (:msg thm) (dissoc thm :msg))))
    (let [[status infos] (p/check-proof def-env (reverse (:params thm)) thm-name (:type thm) method steps)]
      (if (= status :ko)
        (do ;; (println "infos = " infos)
            (throw (ex-info (str "Proof failed: " (:msg infos)) {:theorem thm-name
                                                                 :error (dissoc infos :msg)})))
        (let [new-thm (assoc thm :proof [method steps])]
          (alter-var-root (resolve thm-name) (fn [_] new-thm))
          [:qed thm-name])))))


;;{
;; ## Examples
;;
;; Examples allow to check propositions at the top-level. They are like unrecorded theorems with proofs.
;;
;;}

(s/def ::example (s/cat :params ::def-params
                        :body ::def-body
                        :method #{:script :term}
                        :steps (s/+ any?)))

(declare handle-example-thm)

(defmacro example
  "An example of the form `(example T <method> <steps>)` is the statement of a proposition, as a type `T`, 
as well as a proof. The proof method is either `:script` (declarative proof script) or `:term` (proof term)."
  {:style/indent [2 :form :form [1]]}
  [& args]
  (let [conf-form (s/conform ::example args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Syntax error in example."
                      {:explain (s/explain-str ::example args)}))
      (let [{params :params body :body method :method steps :steps} conf-form
            [status thm] (handle-example-thm params body)]
        (if (= status :ko)
          (throw (ex-info "Cannot check example." thm))
          `(let [[status# infos#] (p/check-proof defenv/empty-env '~(reverse (:params thm)) '~(:name thm) '~(:type thm) '~method '~steps)]
             (if (= status# :ko)
               (do ;; (println "infos = " infos)
                 (throw (ex-info (str "Proof failed: " (:msg infos#)) (dissoc infos# :msg))))
               (do
                 [:checked :example]))))))))

(defn handle-example-thm [params ty]
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
        (if (= status :ko)
          [:ko ty']          
          (if (not (ty/proper-type? defenv/empty-env params ty'))
            [:ko {:msg "Example body is not a proper type" :type ty'}]
            [:ok (defenv/->Theorem (gensym "example") params (count params) ty' false)]))))))

;;{
;; ## Implicits
;;}



(s/def ::implicit-header (s/cat :def-env symbol?
                            :ctx symbol?
                            :params (s/+ ::iparam)))

(s/def ::implicit (s/cat :name ::def-name
                         :doc (s/? ::def-doc)
                         :header (s/spec ::implicit-header)
                         :body (s/* any?)))


(s/def ::iparam (s/tuple symbol? symbol?))

(defn mk-impl-doc [name params explanation]
  (str "\n```\n"
       "(" name " " (clojure.string/join " " params) ")"
       "```\n\n"
       (or explanation "")))

(defmacro defimplicit
  [& args]
  (let [conf-form (s/conform ::implicit args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot define implicit: syntax error."
                      {:explain (s/explain-str ::implicit args)}))
      (let [{def-name :name doc :doc header :header body :body}  conf-form
            {def-env :def-env ctx :ctx params :params} header]
        (when (defenv/registered-definition? def-name)
          (println "[Warning] redefinition as implicit"))
        (let [metadata (merge (meta &form) {:doc (mk-impl-doc def-name (mapv first params) doc)})]
          `(do
             (def ~def-name (defenv/->Implicit '~def-name (fn [~def-env ~ctx ~@params] ~@body)))
             (alter-meta! (var ~def-name) #(merge % (quote ~metadata)))
             [:defined :implicit (quote ~def-name)]))))))

(s/def ::implicit*-header (s/cat :def-env symbol?
                                 :ctx symbol?
                                 :ampersand #(= % '&)
                                 :rest-arg symbol?))

(s/def ::implicit* (s/cat :name ::def-name
                          :doc (s/? ::def-doc)
                          :header (s/spec ::implicit*-header)
                          :body (s/* any?)))


(defmacro defimplicit*
  [& args]
  (let [conf-form (s/conform ::implicit* args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot define implicit: syntax error."
                      {:explain (s/explain-str ::implicit* args)}))
      (let [{def-name :name doc :doc header :header body :body}  conf-form
            {def-env :def-env ctx :ctx rest-arg :rest-arg} header]
        (when (defenv/registered-definition? def-name)
          (println "[Warning] redefinition as (n-ary) implicit"))
        (let [metadata (merge (meta &form) {:doc (or doc "")})]
          `(do
             (def ~def-name (defenv/->Implicit '~def-name (fn [~def-env ~ctx & ~rest-arg] ~@body)))
             (alter-meta! (var ~def-name) #(merge % (quote ~metadata)))
             [:defined :implicit* (quote ~def-name)]))))))

;;{
;; ## Notations
;;}


(s/def ::notation (s/cat :name ::def-name
                         :doc (s/? ::def-doc)
                         :params (s/coll-of symbol? :kind vector?)
                         :body (s/+ any?)))

(defmacro defnotation
  "Defines a new notation, which is a function called at parsing time. The result must be pair `[status u]`
 with `status` either `:ok` (parsing successful) with `u` the term generated by the notation,
 or `:ko` (parsing failed) and `u` is the error, a map with at least a key `:msg` explaining
 the failure.

Be careful that the parser will be called recursively on the generated term, hence
  recursive definitions must be handled with great care."
  [& args]
  (let [conf-form (s/conform ::notation args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Cannot define notation: syntax error."
                      {:explain (s/explain-str ::notation args)}))
      (let [{def-name :name doc :doc params :params body :body} conf-form]
        (when (defenv/registered-definition? defenv/empty-env def-name)
          (do
            ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
            ;; TODO: maybe disallow redefining if type is changed ?
            ;;       otherwise only warn ?
            (println "[Warning] redefinition as notation: " def-name)))
        `(do
           (def ~def-name
             ~doc
             (defenv/->Notation (quote ~def-name)
               (fn ~params (do ~@body))))
           [:defined :notation (quote ~def-name)])))))


;;{
;; ## Basic forms
;;}


