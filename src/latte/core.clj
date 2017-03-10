(ns latte.core
  "This namespace provides the top-level forms of the LaTTe
  framework. 

  Users (as opposed to developpers) of the framework should
  mostly depend on this namespace."

  (:refer-clojure :exclude [apply])

  (:require [clojure.pprint :as pp]
            [latte.kernel.utils :as u]
            [latte.kernel.presyntax :as stx]
            [latte.kernel.typing :as ty]
            [latte.kernel.norm :as n]
            [latte.kernel.defenv :as defenv]
            [latte.kernel.defs :as d]
            [latte.kernel.proof :as p]))

;;{
;; ## Definitions (defined terms)
;;}

(defn- parse-definition-args [args]
    (when (> (count args) 6)
      (throw (ex-info "Too many arguments for definition" {:max-arity 6 :nb-args (count args)})))
    (when (< (count args) 3)
      (throw (ex-info "Not enough arguments for definition" {:min-arity 2 :nb-args (count args)})))
  (let [[def-name doc params body & opts] args
        def-type (case (count opts)
                   0 nil
                   1 (first opts)
                   2 (second opts)
                   (throw (ex-info "Too many options (please report)" {:opts opts})))]
    (when (not (symbol? def-name))
      (throw (ex-info "Name of definition must be a symbol." {:def-name def-name})))
    (when (not (string? doc))
      (throw (ex-info "Documentation string for definition must be ... a string." {:def-name def-name :doc doc})))
    (when (not (vector? params))
      (throw (ex-info "Parameters of definition must be a vector." {:def-name def-name :params params})))
    [def-name doc params body def-type]))

(defn mk-doc [kind content explanation]
  (str "\n```\n"
       (with-out-str
         (pp/pprint content))
       "```\n**" kind "**: "
       explanation))

(defmacro definition
  "Defines a mathematical term composed of a `name`, and optional (but highly recommended)
  `docstring`, a vector of `parameters` and a `lambda-term` as definitional content.

  An `ex-info` exception is thrown if the term cannot be defined.

  Note that it is a Clojure `def`, the term is defined in the namespace where the `definition` 
  form is invoked."
  [& args]
  (let [[def-name doc params body def-type] (parse-definition-args args)]
    ;; (println "def-name =" def-name " doc =" doc " params =" params " body =" body)
    (when (defenv/registered-definition? {} def-name)
      (do
        ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition as term: " def-name)))
    (let [[status definition] (d/handle-term-definition def-name {} [] params body def-type)]
      (when (= status :ko)
        (throw (ex-info "Cannot define term." {:name def-name, :error definition})))
      (let [quoted-def# definition]
        `(do
           (def ~def-name ~quoted-def#)
           (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                         :doc (mk-doc "Definition" (quote ~body) ~doc)
                                                         :arglists (list (quote ~params)))))
           [:defined :term (quote ~def-name)])))))

;;{
;; ## Definitions of theorems
;;}

(defn- parse-defthm-args [kind args]
    (when (> (count args) 4)
      (throw (ex-info (str "Too many arguments for " kind) {:max-arity 4 :nb-args (count args)})))
    (when (< (count args) 2)
      (throw (ex-info (str "Not enough arguments for " kind) {:min-arity 2 :nb-args (count args)})))
  (let [body (last args)
        params (if (= (count args) 2)
                 []
                 (last (butlast args)))
        doc (if (= (count args) 4)
              (nth args 1)
              "No documentation.")
        def-name (first args)]
    (when (not (symbol? def-name))
      (throw (ex-info (str "Name of " kind " must be a symbol.") {:def-name def-name})))
    (when (not (string? doc))
      (throw (ex-info (str "Documentation string for " kind "must be ... a string.") {:def-name def-name :doc doc})))
    (when (not (vector? params))
      (throw (ex-info (str "Parameters of " kind "must be a vector.") {:def-name def-name :params params})))
    [def-name doc params body]))

(defn- handle-defthm
  "Handling of `defthm` and `deflemma` forms."
  [kind args]
  (let [[def-name doc params ty] (parse-defthm-args (if (= kind :theorem)
                                                      "defthm"
                                                      "deflemma") args)]
    (when (defenv/registered-definition? {} def-name)
      (println "[Warning] redefinition as" (if (= kind :theorem)
                                             "theorem"
                                             "lemma") ":" def-name))
    (let [definition (d/handle-thm-declaration def-name {} params ty)
          metadata {:doc (mk-doc (if (= kind :theorem)
                                   "Theorem"
                                   "Lemma") ty doc)
                    :arglists (list params)
                    :private (= kind :lemma)}]
      [def-name definition metadata])))

(defmacro defthm
  "Declaration of a theorem of the specified `name` (first argument)
  an optional `docstring` (second argument), a vector of `parameters`
 and the theorem proposition (last argument).
 Each parameter is a pair `[x T]` with `x` the parameter name and `T` its
  type. 

  A theorem declared must then be demonstrated using the [[proof]] form."
  [& args]
  (let [[def-name definition metadata] (handle-defthm :theorem args)]
    `(do
       (def ~def-name ~definition)
       (alter-meta! (var ~def-name) #(merge % (quote  ~metadata))) 
       [:declared :theorem (quote ~def-name)])))


(defmacro deflemma
  "Declaration of a lemma, i.e. an auxiliary theorem. In LaTTe a lemma
  is private. To export a theorem the [[defthm]] form must be used instead."
  [& args]
  (let [[def-name definition metadata] (handle-defthm :lemma args)]
    `(do
       (def ~def-name ~definition)
       (alter-meta! (var ~def-name) #(merge % (quote ~metadata))) 
       [:declared :lemma (quote ~def-name)])))

;;{
;; ## Definitions of axioms
;;}

(defn- parse-defaxiom-args [kind args]
    (when (> (count args) 4)
      (throw (ex-info (str "Too many arguments for " kind) {:max-arity 4 :nb-args (count args)})))
    (when (< (count args) 2)
      (throw (ex-info (str "Not enough arguments for " kind) {:min-arity 2 :nb-args (count args)})))
  (let [body (last args)
        params (if (= (count args) 2)
                 []
                 (last (butlast args)))
        doc (if (= (count args) 4)
              (nth args 1)
              "No documentation.")
        def-name (first args)]
    (when (not (symbol? def-name))
      (throw (ex-info (str "Name of " kind " must be a symbol.") {:def-name def-name})))
    (when (not (string? doc))
      (throw (ex-info (str "Documentation string for " kind "must be ... a string.") {:def-name def-name :doc doc})))
    (when (not (vector? params))
      (throw (ex-info (str "Parameters of " kind "must be a vector.") {:def-name def-name :params params})))
    [def-name doc params body]))

(defn- handle-defaxiom
  "Handling of `defaxiom` and `defprimitive` forms."
  [kind args]
  (let [[def-name doc params ty] (parse-defaxiom-args (if (= kind :axiom)
                                                        "defaxiom"
                                                        "defprimitive") args)]
    (when (defenv/registered-definition? {} def-name)
      (println "[Warning] redefinition as" (if (= kind :axiom)
                                             "axiom"
                                             "primitive") ":" def-name))
    (let [definition (d/handle-axiom-declaration def-name {} params ty)
          metadata {:doc (mk-doc (if (= kind :axiom)
                                   "Axiom"
                                   "Primitive") ty doc)
                    :arglists (list params)}]
      [def-name definition metadata])))

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
  (let [[def-name definition metadata] (handle-defaxiom :axiom args)]
    `(do
       (def ~def-name ~definition)
       (alter-meta! (var ~def-name) #(merge % (quote  ~metadata))) 
       [:defined :axiom (quote ~def-name)])))

(defmacro defprimitive
  "Declaration of a primitive, i.e. an axiomatic definition (this is indeed
  a synonymous of [[defaxiom]])."
  [& args]
  (let [[def-name definition metadata] (handle-defaxiom :primitive args)]
    `(do
       (def ~def-name ~definition)
       (alter-meta! (var ~def-name) #(merge % ~metadata)) 
       [:defined :primitive (quote ~def-name)])))

;;{
;; ## Notations
;;}

(defn- parse-notation-args [def-name def-doc def-params def-body]
  (when (not (symbol? def-name))
    (throw (ex-info "Name of notation definition must be a symbol." {:def-name def-name})))
  (when (not (string? def-doc))
    (throw (ex-info "Documentation string for notation definition must be ... a string." {:def-name def-name :doc def-doc})))
  (when (not (vector? def-params))
    (throw (ex-info "Parameters of notation definition must be a vector." {:def-name def-name :params def-params})))
  (when (empty? def-body)
    (throw (ex-info "Empty body in notation definition." {:def-name def-name :body def-body}))))

(defmacro defnotation
  "Defines a new notation, which is a function called at parsing time. The result must be pair `[status u]`
 with `status` either `:ok` (parsing successful) with `u` the term generated by the notation,
 or `:ko` (parsing failed) and `u` is the error, a map with at least a key `:msg` explaining
 the failure.

Be careful that the parser will be called recursively on the generated term, hence
  recursive definitions must be handled with great care."
  [def-name def-doc def-params & def-body]
  (parse-notation-args def-name def-doc def-params def-body)
  (when (defenv/registered-definition? {} def-name)
    (do
      ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
      (println "[Warning] redefinition as notation: " def-name)))
  `(do
     (defn ~def-name
       ~def-doc
       ~def-params
       (defenv/->Notation (quote ~def-name)
         (fn ~def-params (do ~@def-body))))
     [:defined :notation (quote ~def-name)]))

;;{
;; ## Special definitions
;;}

(defn- parse-special-args [def-name def-doc def-params def-body]
  (when (not (symbol? def-name))
    (throw (ex-info "Name of special definition must be a symbol." {:def-name def-name})))
  (when (not (string? def-doc))
    (throw (ex-info "Documentation string for special definition must be ... a string." {:def-name def-name :doc def-doc})))
  (when (not (vector? def-params))
    (throw (ex-info "Parameters of special definition must be a vector." {:def-name def-name :params def-params})))
  (when (< (count def-params) 2)
    (throw (ex-info "Special definition needs at least 2 parameters." {:def-name def-name :params def-params})))
  (when (empty? def-body)
    (throw (ex-info "Empty body in special definition." {:def-name def-name :body def-body}))))

(defmacro defspecial
  "Defines a special term that is computed at typing and/or (delta-)normalization time.
  The term is generated by an arbitrary function called with two arguments: the definitional environment `def-env` and the typing context `ctx` (with value `nil` at normalization time) plus the specific arguments of the special being defined. 

By convention, all specials end with a percent character, cf. e.g. [[type-of%]].

Remark: specials are generally used to simplify proofs, but should be used with care
since they are arbitrary functions. The risk is limited, though, since they cannot 
  introduce inconsistencies, and may at worst generate a looping behavior."
  [def-name def-doc def-params & def-body]
  ;; (println "[defspecial] name=" def-name "params=" def-params)
  (parse-special-args def-name def-doc def-params def-body)
  (when (defenv/registered-definition? {} def-name)
    (do
      ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition as special: " def-name)))
  `(do
     (def ~def-name (defenv/->Special (quote ~def-name)
                      (fn ~def-params (do ~@def-body))))
     (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                   :doc ~def-doc
                                                   :arglists (list (quote ~(vec (rest (rest def-params))))))))
     [:defined :special (quote ~def-name)]))

(defspecial type-of%
  "A special operator such that an occurrence of the
term `(type-of% term)` is replaced by the *type* of `term`."
  [def-env ctx term]
  (let [[status ty] (ty/type-of-term def-env ctx term)]
    (if (= status :ko)
      (throw (ex-info "Cannot synthetize type of term" {:special 'latte.core/type-of% :term term :from ty}))
      ty)))

;; (example
;;  ((:special-fn type-of%) {} '[[x ✳]] 'x)
;;  => ✳)
 

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

(defn apply
  "1. Extract and parse context ctx from args,
  2. Extract and parse type t from args,
  3. Apply fn f on type t in context ctx.

  TODO consider (A) using clojure.core/apply or (B) reversing content of args to
  match clojure.core/apply"
  [f args]
  (let [def-env {}
        ctx (parse-context-args def-env (butlast args))
        t (stx/parse def-env (last args))
        res (f def-env ctx t)]
    (cond
      (instance? java.lang.Boolean res) res
      (or (instance? clojure.lang.Symbol res)
          (instance? clojure.lang.PersistentList res)) (list 'quote res)
      :else (do
              (println "TODO test if (list 'quote res) is really needed.")
              (list 'quote res)))))

;;{
;; ## Top-level term parsing
;;}

(defmacro term [& args]
  (apply (fn [def-env ctx t]
           (if (n/beta-eq? def-env ctx t :kind) '□ t))
         args))

(defmacro type-of [& args]
  (apply (fn [def-env ctx t]
           (ty/type-of def-env ctx t))
         args))

;;{
;; ## Top-level type checking
;;}

(defmacro type-check? [& args]
  (apply (fn [def-env ctx t]
           (n/beta-eq? def-env ctx
                       (stx/parse def-env (last args))
                       (ty/type-of def-env ctx t)))
         (butlast args)))

;;{
;; ## Top-level term equivalence
;;}

(defmacro term= [ctx t1 t2]
  (let [def-env {}
        t1 (stx/parse def-env t1)
        t2 (stx/parse def-env t2)]
    (n/beta-eq? def-env ctx t1 t2)))

;;{
;; ## Proof handling
;;}

(defmacro try-proof
  "Tries (but does not register) a proof of theorem named `thm-name` using the given proof `method`
  and `steps`."
  {:style/indent [2 :form :form [1]]}
  [thm-name method & steps]
  (let [def-env {}
        [status thm] (defenv/fetch-definition def-env thm-name)]
    (if (= status :ko)
      [:ko {:msg "No such theorem." :name thm-name}]
      (let [[status proof-term local-defs]
            (p/check-proof def-env (reverse (:params thm)) thm-name (:type thm) method steps)]
        (if (= status :ko)
          (if (= (get proof-term :info)
                 :proof-incomplete)
            ;; proof is incomplete
            `[:ko {:proof-incomplete (quote ~thm-name)}]
            ;; real error
            (let [res [:ko {:msg (str "Proof failed: " (:msg proof-term))
                            :theorem thm-name
                            :error (dissoc proof-term :msg)}]]
              (list 'quote res)))
          ;; proof is ok
          `(do
             [:ok {:proof-of (quote ~thm-name)}]))))))

(defmacro proof
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
  (let [def-env {}
        [status thm] (defenv/fetch-definition def-env thm-name)]
    (when (= status :ko)
      (throw (ex-info "No such theorem." {:name thm-name})))
    (let [[status proof-term local-defs]
          (p/check-proof def-env (reverse (:params thm)) thm-name (:type thm) method steps)]
      (if (= status :ko)
        (throw (ex-info (str "Proof failed: " (:msg proof-term)) {:theorem thm-name
                                                                  :error (dissoc proof-term :msg)}))
        (let [new-thm (assoc thm :proof proof-term)]
          ;; TODO: integrate local-defs ?  or register proof ?
          ;;(println new-thm#)
          (alter-var-root (resolve thm-name) (fn [_] new-thm))
          `(do
             ;;(alter-var-root (var ~thm-name) (fn [_#] ~new-thm#))
             [:qed (quote ~thm-name)]))))))

;;{
;; ## Indentation rules
;;}


(defnotation lambda
  "The `lambda` notation for abstractions.

The simplest form is `(lambda [x T] e)` with
as `bindings` the variable `x` of type `T`, and
`e` as the abstraction `body`.

The low-level equivalent is `(λ [x T] e)`.

The extended notation `(lambda [x y z T] e)` is
equivalent to `(lambda [x T] (lambda [y T] (lambda [z T] e)))`."
  [bindings body]
  [:ok (list 'λ bindings body)])

(alter-meta! #'lambda update-in [:style/indent] (fn [_] [1 :form :form]))

(defnotation forall
  "The `lambda` notation for product abstractions.

The expression `(forall [x T] U)` is the type of an
abstraction of the form `(lambda [x T] e)` with `e`
 of type `U` when `x` is of type `P`.

The low-level equivalent is `(Π [x T] U)`.

The extended notation `(forall [x y z T] U)` is
equivalent to `(forall [x T] (forall [y T] (forall [z T] U)))`."
  [bindings body]
  [:ok (list 'Π bindings body)])

(alter-meta! #'forall update-in [:style/indent] (fn [_] [1 :form :form]))

(defnotation ==>
  "The function type, or equivalently logical implication.

  `(==> A B)` is `(Π [x A] B)` where `x` does not occur free in `B`.

Implication is right associative:

'(==> A B C) ≡ `(==> A (==> B C))`."
  [& arguments]
  [:ok (list* '⟶ arguments)])

(defmacro assume
  {:style/indent [1 :form [1]]} 
  [bindings & body]
  `((quote assume) ~bindings ~body))

(defmacro have
  {:style/indent [1]}
  [& args]
  `((quote have) ~@args))

(defmacro pose
  {:style/indent [1]}
  [& args]
  `((quote pose) ~@args))

(defmacro qed
  [& args]
  `((quote qed) ~@args))
