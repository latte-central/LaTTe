
;;{
;; # Top-level LaTTe forms and utilities
;;
;; In this namespace the main user-level syntactic forms of the
;; LaTTe proof assistant are defined.
;;}

(ns latte.core
  "This namespace provides the top-level forms of the LaTTe
  framework."

  (:require [clojure.spec.alpha :as s]
            [clojure.pprint :as pp]
            [taoensso.timbre :as log]
            [latte-kernel.presyntax :as stx]
            [latte-kernel.unparser :as unparser]
            [latte-kernel.typing :as ty]
            [latte-kernel.norm :as n]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :as p]
            [latte.utils :as u]
            [latte.parse :as parse]
            [latte.certify :as cert]
            [latte.search :as search])
)


;;{
;; The unparser takes low-level lambda-terms and try
;; to give them some readability.
;; For users, this is mostly useful for understanding the
;; reasons why a statement or a proof would fail.
;;
;; It is also a nice debugging aid when developping/extending
;; the proof assistant itself.
;;
;; Unparsers are installed in an imperative way, and the following
;; installs the most basic ones (e.g. recognizing implications vs.
;; dependent products, simplifying nested implications, etc.)
;; A few more important unparsers are installed by the standard library.
;;}

;; Initialization of unparser
(unparser/install-fundamental-unparsers!)

;; Initialization of opacity manager in proofs
(p/install-opacity-function u/set-opacity!)

;;{
;; ## Definitions
;;
;; Mathematical developments always start with the definition of
;; mathematical concepts.
;;
;; In LaTTe this is handled by the `definition' top-level form.
;; The following *spec* describes the grammar of this form.
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

;;{
;; The `definition` macro is defined below.
;;}

(declare handle-implicit-type-parameters)
(declare handle-term-definition)
(declare mk-def-doc)
(declare defimplicit)

(defmacro definition
  "Defines a mathematical term with the following structure:

  
      (definition <name>
        \"<docstring>\"
        [[x1 T1] ... [xN TN]] ;; <params>
        <body>)


  composed of a `name`, and optional (but highly recommended)
  `docstring`, a vector `params` of parameters (typed variables) and
  `body` (a lambda-term) as definitional content.

  An `ex-info` exception is thrown if the term cannot be defined.

  Note that a definition is a `def` in the Clojure sense, the term is defined in the namespace where the `definition` 
  form is invoked."
  [& args]
  ;;{
  ;;  - First, we check the arguments syntax according to the spec grammar.
  ;;}
  (let [[status msg infos] (parse/parse-definition :definition args)]
    (if (= status :ko)
      (throw (ex-info (str "Cannot define term: " msg)
                      infos))
      (let [{def-name :name doc :doc params :params body :body} infos]
        ;; handling of implicit parameter types
        (if-let [res (u/fetch-implicit-type-parameters params)]
          (handle-implicit-type-parameters `definition def-name doc (:rest-params res) body
                                           (:implicit-types res)
                                           (map first (:explicit-type-params res))
                                           (symbol (str def-name "-def"))
                                           (into [] (concat (:explicit-type-params res) (:rest-params res))))
          ;; no implicit parmeter types from here...
          (let [[status definition] (handle-term-definition def-name params body)]
            (when (= status :ko)
              (throw (ex-info "Cannot define term." {:name def-name, :error definition})))
            (when (defenv/registered-definition? def-name)
              (log/warn "Redefinition as term: " def-name))
            ;;{
            ;;  - Second, after some checks, we register the definition in the currently active namespace (i.e. `*ns*`).
            ;;}          
            (let [quoted-def# definition]
              `(do
                 (def ~def-name ~quoted-def#)
                 (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                               :doc (mk-def-doc "Definition" (quote ~body) ~doc)
                                                               :arglists (list (quote ~params)))))
                 [:defined :term (quote ~def-name)]))))))))


(defmacro try-definition
  "Try to make the [[definition]] without registering it, and without throwing exceptions in case of error.
This is used to inspect definition errors."
  [& args]
  ;;{
  ;;  - First, we check the arguments syntax according to the spec grammar.
  ;;}
  (let [[status msg infos] (parse/parse-definition :definition args)]
    (if (= status :ko)
      [:error msg infos]
      (let [{def-name :name doc :doc params :params body :body} infos]
        ;; handling of implicit parameter types
        (if-let [res (u/fetch-implicit-type-parameters params)]
          `[:error {:msg "Cannot use implicit parameters with `try-definition`" :implicit-types (quote ~(:implicit-types res))}]
          ;; no implicit parmeter types from here...
          (let [[status definition] (handle-term-definition def-name params body)]
            (println "def:" status definition)
            (if (= status :ko)
              `[:error (quote ~definition)]
              `[:valid :definition (quote ~def-name)])))))))

;;{
;; The next function implements the support of *implicit type parameters*.
;;}

(declare gen-type-parameters-defimplicit)

(defn ^:no-doc def-kind-infos [def-kind]
  (case def-kind
    latte.core/definition ["Definition" :definition]
    latte.core/defthm ["Theorem" :theorem]
    latte.core/deflemma ["Lemma" :lemma]
    latte.core/defaxiom ["Axiom" :axiom]
    (throw (ex-info "Definition kind not supported." {:def-kind def-kind}))))

(defn ^:no-doc handle-implicit-type-parameters
  [def-kind def-name doc params body implicit-types implicit-types-params explicit-def-name explicit-params]
  (let [[def-kind-name def-kind-kw] (def-kind-infos def-kind)]
    `(do
       (~def-kind ~explicit-def-name ~(str "This is an explicit variant of [[" def-name "]].") ~explicit-params ~body)
       (alter-meta! (var ~explicit-def-name) update-in [:no-doc] (fn [_#] true))
       ~(gen-type-parameters-defimplicit def-name def-kind-name doc explicit-def-name implicit-types implicit-types-params params explicit-params body)
       (alter-meta! (var ~def-name) update-in [:arglists] (fn [_#] (list (quote ~params))))
       [:declared ~def-kind-kw (quote ~explicit-def-name) :implicit (quote ~def-name)])))

;;{
;; The following function generates a `defimplicit` form that (if successful) synthesizes
;; the arguments for implicit type parameters.
;; An exception is raised if the synthesis fails (which means no implicity-type-parameter handler
;; is found).
;;}

(defn ^:no-doc gen-type-parameters-defimplicit
  "Generate the defimplicit for definitions with implicit type parameters."
  [def-name def-kind doc explicit-def-name implicit-types implicit-types-params real-params explicit-params body]
  (let [def-env-var (gensym "def-env")
        ctx-var (gensym "ctx")
        ndoc (mk-def-doc def-kind body doc)
        [targs defparams] (reduce (fn [[targs defparams] [param param-ty]]
                                    (if (contains? implicit-types param)
                                      [targs defparams]
                                      (let [param-ty-var (gensym (str param "-ty"))]
                                        [(conj targs [param-ty-var param-ty])
                                         (conj defparams [(gensym param) param-ty-var])])))
                                  [[] []] explicit-params)
        [remaining-implicit-types lt-clauses] 
        (reduce (fn [[itypes lt-clauses] param]
                  (let [[itypes' lt-clause] 
                        (u/fetch-implicit-type-parameter-handler itypes def-env-var ctx-var param)]
                    [itypes' (if (nil? lt-clause)
                               lt-clauses
                               (conj lt-clauses (first lt-clause) (second lt-clause)))])) [implicit-types []] targs)]
    (when-not (empty? remaining-implicit-types)
      (throw (ex-info "Unsolved implicit type parameters" {:statement def-name
                                                           :implicit-type-params (into #{} (map #(symbol (str "?" (name %))) implicit-types))
                                                           :unsolved (into #{} (map #(symbol (str "?" (name %))) remaining-implicit-types))})))
    `(defimplicit ~def-name
       ~ndoc
       [~def-env-var ~ctx-var ~@defparams]
       (let [~@lt-clauses]
         (list (var ~explicit-def-name) ~@(concat implicit-types-params
                                                  (map first defparams)))))))

;;{
;; The following function parse a sequence of terms, the `params` (parameters),
;; using LaTTe *presyntax* (in namespace `latte-kernel.presyntax`).
;;}

(defn ^:no-doc parse-parameters
  [def-env params]
  (reduce (fn [[sts params] [x ty]]
            (let [[status ty] (stx/parse-term def-env ty)]
              (if (= status :ko)
                (reduced [:ko ty])
                [:ok (conj params [x ty])]))) [:ok []] params))


;;{
;; The following is how we handle the definitions.
;;}

(defn ^:no-doc handle-term-definition [def-name params body]
  ;;{
  ;;  - At this stage the definition is of the form:
  ;;
  ;; 
  ;;     (definition <def-name> [<params> ...] <body>)
  ;; 
  ;;
  ;;  - Step 1: we parse the parameters (`params`) of the definiton
  ;;}
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      ;;{
      ;;  - Step 2: the `body` of the definition is also parsed.
      ;;}
      (let [[status body-term] (stx/parse-term defenv/empty-env body)]
        (if (= status :ko)
          [:ko body-term]
          ;;{
          ;;  - Step 3: the type of the definition is computed based on the parsed parameters and body
          ;;  (in the empty definitional environment because we use the current namespace implicitly)
          ;;}
          (let [[status ty _] (try (ty/type-of-term defenv/empty-env params body-term)
                                   (catch Exception e [:ko {:msg (ex-message e) :info (ex-info e)}]))]
            (if (= status :ko)
              `[:ko (quote ~ty)]
              ;;{
              ;; If Step 1-3 went well, the definition is created and returned
              ;;}
              [:ok (defenv/->Definition def-name params (count params) body-term #{} ty {})])))))))

;;{
;; The following function generates the clojure documentation of
;; the definition, based on the provided `explanation` and `content`.
;; The same function will be used to generate the documentation
;; of other `kind` of statements such as theorems or axioms.
;;}

(defn ^:no-doc mk-def-doc 
  [kind content explanation]
  (str "\n```\n"
       (with-out-str
         (pp/pprint content))
       "```\n**" kind "**: "
       (or explanation "")))

;;{
;; ## Theorems, lemmas and axioms
;;
;; **Theorems** (of category `:theorem`) are the "bread and butter" of the mathematical developments.
;; Based on their definition, the properties of mathematical contents
;; are stated as theorem statements, which must then be demonstrated
;; by a *proof*.
;;
;; **Lemmas** (of category `:lemma`) are often considered auxiliary results that may be used
;; as intermediate steps towards the demonstration of higher-level
;; theorems. In LaTTe lemmas are considered "private" theorems,
;; similarly to what `defn-' is to `defn'.
;;
;; Finally, **axioms** (of category `:axiom`) are either unprovable or sometimes "hard to prove"
;; statements that are considered true without a proof.
;;
;; All these are slightly different but roughly similar  *mathematical statements*:
;; - theorems must have an attached proof, and are registered publicly
;; - lemmas also have an attached proof, but are not registered publicly
;; - axioms do *not* have a proof, and are registered publicly
;;
;; We can thus say that all these are slightly distinct form of "theorem", so
;; we handle them in a generic way.
;;
;; In each case the first step is to check the conformance of the syntax according
;; to its *spec*.
;;}

(defn ^:no-doc conform-statement
  [category args]
  (let [[status msg infos] (parse/parse-definition category args)]
    (if (= status :ko)
      (throw (ex-info (str "Cannot declare " (name category) ": " msg) infos))
      infos)))

;;{
;; Now the maing handling of theorem-like statements is with the following function,
;; taking a `category` (either `:theorem`, `:lemma` or  `:axiom`), a vector `params` of
;; parameters and the statement itself as a type `ty`.
;;}

(declare safe-property-type?
         build-statement)

(defn ^:no-doc handle-statement
  [category thm-name params body]
  ;;{
  ;;  - We first check the conformance of the statement according to its *spec*.
  ;;}
  
    (when (defenv/registered-definition? thm-name)
      (log/warn (str "Redefinition as " (name category) ":") thm-name))
    ;;{
    ;; and then we proceed with the main steps:
    ;;
    ;;  - Step 1: we parse the parameters (`params`) of the statement
    ;;}
    (let [[status params] (parse-parameters defenv/empty-env params)]
      (if (= status :ko)
        [:ko params]
        ;;{
        ;;  - Step 2: the `body` of the statement is also parsed.
        ;;}
        (let [[status body-term] (stx/parse-term defenv/empty-env body)]
          (if (= status :ko)
            [:ko body-term]
            ;;{
            ;; - Step 3: we check that the statement is a proper type.
            ;;}
            (let [[status infos] (try (if (ty/proper-type? defenv/empty-env params body-term)
                                        [:ok true]
                                        [:ok false])
                                      (catch Exception e [:ko {:msg (ex-message e)
                                                               :data (ex-data e)}]))]
              (cond 
                (= status :ko)
                [:ko infos]
                (false? infos)
                [:ko {:msg (str "Body of " (name category) " is not a proper type") :statement thm-name :category category :body (unparser/unparse body-term)}]
                :else
                ;;{
                ;;  - Step 4: if all went well, we construct the internal representation.
                ;;}
                [:ok (build-statement category thm-name params body-term)])))))))


;;{
;; The `proper-type?` predicate of the kernel might throw an exception
;;}

;;{
;; The following function builds the internal representation of a statement
;; according to its `category`. Internally we distinguish between theorems/lemmas
;; on the one side, and axioms on the other side.
;;}

(defn ^:no-doc build-statement
  [category thm-name params ty]
  (case category
    (:theorem :lemma) (defenv/->Theorem thm-name params (count params) ty nil)
    :axiom (defenv/->Axiom thm-name params (count params) ty)
    (throw (ex-info "Cannot build statement: not a statement category (please report)"
                    {:category category
                     :thm-name thm-name}))))

;;{
;; The function below prepares the required metatadata associated to a statement.
;;}

(defn ^:no-doc statement-metadata
  [category doc params body]
  {:doc (mk-def-doc (clojure.string/capitalize (name category)) body doc)
   :arglists (list params)
   :body body
   :private (= category :lemma)})


(defn ^:no-doc define-statement!
  [category def-name definition metadata]
  `(do
     (def ~def-name ~definition)
     (alter-meta! (var ~def-name) #(merge % (quote ~metadata))) 
     [:declared ~category (quote ~def-name)]))

;;{
;; ### Theorems
;;
;; The most general form is `defthm' to define theorems.
;;}

(s/def ::theorem (s/cat :name ::def-name
                        :doc (s/? ::def-doc)
                        :params ::def-params
                        :body ::def-body))

(defmacro defthm
  "Declaration of a theorem of the following form:

      (defthm <name>
        \"<docstring>\"
        [[x1 T1] ... [xN TN]] ;; <params>
        <body>)

  with the specified `name` (first argument)
  an optional `docstring` (second argument), a vector `params` of parameters
  and the theorem proposition as `body` (last argument).
 Each parameter is a pair `[x T]` with `x` the parameter name and `T` its
  type. 

  A theorem declared must later on be demonstrated using the [[proof]] form.
  As a side effect, the statement of the theorem is recorded in the current
  namespace (i.e. it is a Clojure `def`)."
  [& args]
  (let [{thm-name :name doc :doc params :params body :body}
        (conform-statement :theorem args)]
            ;; handling of implicit parameter types
    (if-let [res (u/fetch-implicit-type-parameters params)]
      (handle-implicit-type-parameters `defthm thm-name doc (:rest-params res) body
                                       (:implicit-types res)
                                       (map first (:explicit-type-params res))
                                       (symbol (str thm-name "-thm"))
                                       (into [] (concat (:explicit-type-params res) (:rest-params res))))
      ;; no implicit type parameters
      (let [[status result] (handle-statement :theorem thm-name params body)]
        (if (= status :ko)
          (throw (ex-info "Cannot declare theorem." result))
          (let [metadata (statement-metadata :theorem doc params body)]
            (define-statement! :theorem thm-name result metadata)))))))

(defmacro try-defthm
  "A try-only version of [[defthm]] (does not register theorem in case of success)"
  [& args]
  (let [{thm-name :name doc :doc params :params body :body}
        (conform-statement :theorem args)]
            ;; handling of implicit parameter types
    (if-let [res (u/fetch-implicit-type-parameters params)]
      (handle-implicit-type-parameters `defthm thm-name doc (:rest-params res) body
                                       (:implicit-types res)
                                       (map first (:explicit-type-params res))
                                       (symbol (str thm-name "-thm"))
                                       (into [] (concat (:explicit-type-params res) (:rest-params res))))
      ;; no implicit type parameters
      (let [[status result] (handle-statement :theorem thm-name params body)]
        (if (= status :ko)
          `[:error (quote ~result)]
          `[:valid :theorem (quote ~thm-name)])))))

;;{
;; ### Lemmas
;;
;; A lemma is a theorem that is not exported, i.e. it remains private
;; in the namespace where it is defined (it is still available as a
;; Clojure var).
;;}

(defmacro deflemma
  "Declaration of a lemma, i.e. an auxiliary theorem. In LaTTe a lemma
  is private. To export a theorem the [[defthm]] form must be used instead.
  Otherwise the two forms are the same."
  [& args]
  (let [{thm-name :name doc :doc params :params body :body}
        (conform-statement :lemma args)]
    (if-let [res (u/fetch-implicit-type-parameters params)]
      (handle-implicit-type-parameters `deflemma thm-name doc (:rest-params res) body
                                       (:implicit-types res)
                                       (map first (:explicit-type-params res))
                                       (symbol (str thm-name "-lemma"))
                                       (into [] (concat (:explicit-type-params res) (:rest-params res))))
      ;; no implicit type parameters
      (let [[status result] (handle-statement :lemma thm-name params body)]
        (if (= status :ko)
          (throw (ex-info "Cannot declare lemma." result))
          (let [metadata (statement-metadata :lemma doc params body)]
            (define-statement! :lemma thm-name result metadata)))))))

;;{
;; ### Axioms
;;
;; An axiom is like a theorem but whose proof is assumed.
;; It is a good practice to rely on the minimum amount of axioms,
;; although they cannot be avoided in general (e.g. for classical logic,
;; for the definite descriptor, for set equality, etc.).
;;}

(s/def ::axiom (s/cat :name ::def-name
                      :doc (s/? ::def-doc)
                      :params ::def-params
                      :body ::def-body))


(defmacro defaxiom
  "Declaration of an axiom of the form:

      (defaxiom <name>
        \"<docstring>\"
        [[x1 T1] ... [xN TN]] ;; <params>
        <body>)

  with the specified `name` (first argument)
  an optional `docstring` (second argument), a vector `params` of parameters
 and the axiom `body`, the axiom statement as a lambda-term (last argument).
 Each parameter is a pair `[x T]` with `x` the parameter name and `T` its
  type. 

  An axiom is accepted without a proof, and should thus be used with
extra care. The LaTTe rule of thumb is that theorems should be
favored, but axioms are sometimes required (e.g. the law of the excluded
 middle) or more \"reasonable\" because of the proof length or complexity.
In all cases the introduction of an axiom must be justified with strong
 (albeit informal) arguments."
  [& args]
  (let [{thm-name :name doc :doc params :params body :body}
        (conform-statement :axiom args)]
    (if-let [res (u/fetch-implicit-type-parameters params)]
      (handle-implicit-type-parameters `defaxiom thm-name doc (:rest-params res) body
                                       (:implicit-types res)
                                       (map first (:explicit-type-params res))
                                       (symbol (str thm-name "-ax"))
                                       (into [] (concat (:explicit-type-params res) (:rest-params res))))
      ;; no implicit type parameters
      (let [[status result] (handle-statement :axiom thm-name params body)]
        (if (= status :ko)
          (throw (ex-info "Cannot declare axiom." result))
          (let [metadata (statement-metadata :axiom doc params body)]
            (define-statement! :axiom thm-name result metadata)))))))

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

(s/def ::pose-args (s/cat :pose-name symbol?
                          :def-kw #(= % :=)
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
      `[:have (quote ~have-name) (quote ~have-type) (quote ~have-term) ~(assoc (or infos {})
                                                                               :pose false)])))

(defmacro pose
  "A local definition `(pose P := e)` allows a proof to refer to term `e` under
the name `P` in a proof. This is equivalent to `(have P _ :by e)` (with the type of
`e` inferred)."
  [pose-name pose-kw pose-term]
  (let [infos (meta &form)
        conf-form (s/conform ::pose-args (rest &form))]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Pose step syntax error."
                      {:infos infos
                       :explain (s/explain-str ::pose-args (rest &form))}))
      `[:have (quote ~pose-name) (quote ~(symbol "_")) (quote ~pose-term) ~(assoc (or infos {})
                                                              :pose true)])))



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


(defn try-proof
  "Provides a proof of theorem named `thm-name` using the given proof `steps`.
  This version only checks if the proof is correct or not, use the [[proof]] function
  for actually registering the proof."
  {:style/indent [1 :form [1]]}
  [thm-name & steps]
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
    (if (= status :ko)
      [:failed thm]
      (let [[status infos] (p/check-proof def-env (reverse (:params thm)) thm-name (:type thm) steps)]
        (if (= status :ko)
          (do ;; (println "infos = " infos)
            [:failed thm-name infos])
          (let [new-thm (assoc thm :proof steps)]
            ;; (alter-var-root (resolve thm-name) (fn [_] new-thm))
            [:qed thm-name]))))))


(def ^:dynamic *proof-certification-enabled* true)

(defn proof
  "Provides a proof of theorem named `thm-name` using the given proof `steps`."
  {:style/indent [1 :form [1]]}
  [thm-name & steps]
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
    (let [certified-proof?
          (and *proof-certification-enabled*
               (cert/proof-certified? *ns* thm-name (:params thm) (:type thm) steps))]
      #_(when certified-proof?
        (println (str "[proof] theorem '" *ns* "/" thm-name "' has certified proof")))
      (let [[status infos] (if certified-proof?
                             [:ok {}]
                             (p/check-proof def-env (reverse (:params thm)) thm-name (:type thm) steps))]
        (if (= status :ko)
          (do ;; (println "infos = " infos)
            (throw (ex-info (str "Proof failed: " (:msg infos)) {:theorem thm-name
                                                                 :error (dissoc infos :msg)})))
          (let [new-thm (assoc thm :proof steps)]
            (alter-var-root (resolve thm-name) (fn [_] new-thm))
            [:qed thm-name]))))))


;;{
;; ## Examples
;;
;; Examples allow to check propositions at the top-level. They are like unrecorded theorems with proofs.
;;
;;}

(s/def ::example (s/cat :params ::def-params
                        :body ::def-body
                        :steps (s/+ any?)))

(declare handle-example-thm)

(defmacro example
  "An example of the form `(example T <steps>)` is the statement of a proposition, as a type `T`, 
as well as a proof."
  {:style/indent [2 :form :form [1]]}
  [& args]
  (let [conf-form (s/conform ::example args)]
    (if (= conf-form :clojure.spec.alpha/invalid)
      (throw (ex-info "Syntax error in example."
                      {:explain (s/explain-str ::example args)}))
      (let [{params :params body :body steps :steps} conf-form
            [status thm] (handle-example-thm params body)]
        (if (= status :ko)
          (throw (ex-info "Cannot check example." thm))
          `(let [[status# infos#] (p/check-proof defenv/empty-env '~(reverse (:params thm)) '~(:name thm) '~(:type thm) ~steps)]
             (if (= status# :ko)
               (do ;; (println "infos = " infos)
                 (throw (ex-info (str "Proof failed: " (:msg infos#)) (dissoc infos# :msg))))
               (do
                 [:checked :example]))))))))

(defn ^:no-doc handle-example-thm [params ty]
  (let [[status params] (parse-parameters defenv/empty-env params)]
    (if (= status :ko)
      [:ko params]
      (let [[status ty'] (stx/parse-term defenv/empty-env ty)]
        (if (= status :ko)
          [:ko ty']          
          (if (not (ty/proper-type? defenv/empty-env params ty'))
            [:ko {:msg "Example body is not a proper type" :type ty'}]
            [:ok (defenv/->Theorem (gensym "example") params (count params) ty' false)]))))))

(defmacro try-example
  "This is the same as [[example]] but without throwing exceptions."
  {:style/indent [2 :form :form [1]]}
  [& args]
  `(try (example ~@args)
        (catch Exception e#
          [:failed (.getMessage e#) (ex-data e#)])))

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


(s/def ::iparam any?) ;; (s/tuple symbol? symbol?))

(defn ^:no-doc mk-impl-doc [name explanation]
  ;; XXX: everything in the explanation ?
  explanation)

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
        (let [metadata (merge (meta &form) {:doc (mk-impl-doc def-name doc)})]
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


(defimplicit the-type-of
  "Replaces the provided term by its inferred type."
  [def-env ctx [term typ]]
  typ)

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
;; ## Top-level term parsing
;;}

(defn- parse-context-args [def-env args]
  (loop [args args, ctx []]
    (if (seq args)
      (do
        (when (not (and (vector? (first args))
                        (= (count (first args)) 2)))
          (throw (ex-info "Context argument must be a binding pair." {:argument (first args)})))
        (let [[x ty] (first args)
              ty' (stx/parse def-env ty)]
          (when (not (symbol? x))
            (throw (ex-info "Binding variable  must be a symbol." {:argument (first args) :variable x})))
          (when (not (ty/proper-type? def-env ctx ty'))
            (throw (ex-info "Binding type is not a type." {:argument (first args) :binding-type ty})))
          (recur (rest args) (cons [x ty'] ctx))))
      (do ;; (println "[parse-context-args] ctx=" ctx)
          ctx))))

(defmacro term 
  "Parse a LaTTe term at the top-level. A context can be provided
  in the form of a serie of `[var type]` pairs before the actual term."
  [& args]
  (let [def-env defenv/empty-env
        t (stx/parse def-env (last args))
        ctx (parse-context-args def-env (butlast args))]
    ;; (println "[term] t = " t " ctx = " ctx)
    (if (latte-kernel.norm/beta-eq? def-env ctx t :kind)
      '□
      (let [ty (ty/type-of def-env ctx t)]
        (list 'quote (latte-kernel.unparser/unparse t))))))

(defmacro term-eq? 
  "Checks if two terms `t` and `u` are equal in the sense of
  having the \"same\" normal form (up-to alpha-conversion, the
  safe renaming of bound variables.

  A context can be provided
  in the form of a serie of `[var type]` pairs before the actual term."
  [& args]
  (let [def-env defenv/empty-env
        t2 (stx/parse def-env (last args))
        t1 (stx/parse def-env (last (butlast args)))
        ctx (parse-context-args def-env (butlast (butlast args)))]
    ;; (println "[term] t = " t " ctx = " ctx)
    (latte-kernel.norm/beta-eq? def-env ctx t1 t2)))

;;{
;; ## Top-level type checking
;;}

(defmacro type-of 
  "Give the type of a term `t` in a context at the top-level. 
  To only parse the term use [[term]]."
  [& args]
  (let [def-env defenv/empty-env
        t (stx/parse def-env (last args))
        ctx (parse-context-args def-env (butlast args))]
    (let [ty (ty/type-of def-env ctx t)]
      (list 'quote (latte-kernel.unparser/unparse ty)))))

(defmacro type-check?
  "Check if a term `t` in of the specified type `ty`.
  A context can be specified as with [[type-of]]."
  [& args]
  (let [def-env defenv/empty-env
        t (stx/parse def-env (last (butlast args)))
        ty (stx/parse def-env (last args))
        ctx (parse-context-args def-env (butlast (butlast args)))]
    ;;(println "[check-type?] ctx=" ctx)
    (let [tty (ty/type-of def-env ctx t)]
      (n/beta-eq? def-env ctx ty tty))))

;;{
;; ## Search facilities (re-exported)
;;}

(defn search-theorem
  "Search a theorem using pattern `patt`.
  A pattern (generally quoted) is either:
    - any clojure value, that has to be matched exactly, with
      the exception of a symbol starting with a question mark (denoting a variable)
    - a simple variable `?X` that can match anything
    - a list/sequence of patterns `(patt1 patt2 ...)`
    - a zero-or-many variable `?Y*` that matches zero or more times greedily 
    - a one-or-many variable `?Z+` that matches at least once greedily
    - an optional variable `?V?` that matches at most once
  The optional argument `where` is the name (symbol) of a namespace where
the search must be applied (by default, use all registered namespaces)

The special variables `?_`, `?_*`,  `?_+` and `?_?` produce no binding when matched.

  The result is a vector of matches, each match being a pair `[theorem-var match-env]`
  with `theorem-var` the reference to the theorem as a clojure var,
 and `match-env` the variable bindings corresponding to the match.
"
  ([patt] (search/search-theorem patt))
  ([where patt] (search/search-theorem where patt)))

;;{
;; ## Basic forms
;;}

(defn forall
  "The universal quantifier `(forall [x A] t)` is ∀x:A.t (or Πx:A.t in type theory).
  
  As a syntactic sugar an expression of form `(forall [x y z A] t)`
  translates to `(forall [x A] (forall [y A] (forall [z A] t)))`"
  {:style/indent [1 :form :form]}
  [params body]
  (list 'forall params body))

(defn lambda  
  "The abstraction `(lambda [x A] t)` is λx:A.t.
  
  As a syntactic sugar an expression of form `(lambda [x y z A] t)`
  translates to `(lambda [x A] (lambda [y A] (lambda [z A] t)))`"
  {:style/indent [1 :form :form]}
  [params body]
  (list 'lambda params body))

