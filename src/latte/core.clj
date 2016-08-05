(ns latte.core
  "This namespace provides the top-level forms of the LaTTe
  framework. 

  Users (as opposed to developpers) of the framework should
  mostly depend on this namespace."

  (:require [clojure.pprint :as pp])

  (:require [latte.kernel.utils :as u])
  (:require [latte.kernel.presyntax :as stx])
  (:require [latte.kernel.typing :as ty])
  (:require [latte.kernel.norm :as n])
  (:require [latte.kernel.defenv :as defenv])
  (:require [latte.kernel.defs :as d])
  (:require [latte.kernel.proof :as p])
  )

;;{
;; ## Definitions (defined terms)
;;}

(defn parse-definition-args [args]
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
       "```\n**" kind "**"
       "\n\n"
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

(defn parse-defthm-args [args]
    (when (> (count args) 4)
      (throw (ex-info "Too many arguments for defthm" {:max-arity 4 :nb-args (count args)})))
    (when (< (count args) 2)
      (throw (ex-info "Not enough arguments for defthm" {:min-arity 2 :nb-args (count args)})))
  (let [body (last args)
        params (if (= (count args) 2)
                 []
                 (last (butlast args)))
        doc (if (= (count args) 4)
              (nth args 1)
              "No documentation.")
        def-name (first args)]
    (when (not (symbol? def-name))
      (throw (ex-info "Name of defthm must be a symbol." {:def-name def-name})))
    (when (not (string? doc))
      (throw (ex-info "Documentation string for defthm must be ... a string." {:def-name def-name :doc doc})))
    (when (not (vector? params))
      (throw (ex-info "Parameters of defthm must be a vector." {:def-name def-name :params params})))
    [def-name doc params body]))

(defmacro defthm
  [& args]
  (let [[def-name doc params ty] (parse-defthm-args args)]
    ;;(println "def-name =" def-name " doc =" doc " params =" params " ty =" ty)
    (when (defenv/registered-definition? {} def-name)
      (do
        ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition as theorem: " def-name)))
    (let [definition (d/handle-thm-declaration def-name {} params ty)
          quoted-def# definition]
      `(do
         (def ~def-name ~quoted-def#)
         (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                       :doc (mk-doc "Theorem" (quote ~ty) ~doc)
                                                       :arglists (list (quote ~params)))))
         [:declared :theorem (quote ~def-name)]))))

;;{
;; ## Definitions of axioms
;;}

(defn parse-defaxiom-args [args]
    (when (> (count args) 4)
      (throw (ex-info "Too many arguments for defaxiom" {:max-arity 4 :nb-args (count args)})))
    (when (< (count args) 2)
      (throw (ex-info "Not enough arguments for defaxiom" {:min-arity 2 :nb-args (count args)})))
  (let [body (last args)
        params (if (= (count args) 2)
                 []
                 (last (butlast args)))
        doc (if (= (count args) 4)
              (nth args 1)
              "No documentation.")
        def-name (first args)]
    (when (not (symbol? def-name))
      (throw (ex-info "Name of defaxiom must be a symbol." {:def-name def-name})))
    (when (not (string? doc))
      (throw (ex-info "Documentation string for defaxiom must be ... a string." {:def-name def-name :doc doc})))
    (when (not (vector? params))
      (throw (ex-info "Parameters of defaxiom must be a vector." {:def-name def-name :params params})))
    [def-name doc params body]))

(defmacro defaxiom
  [& args]
  (let [[def-name doc params ty] (parse-defaxiom-args args)]
    ;;(println "def-name =" def-name " doc =" doc " params =" params " ty =" ty)
    (when (defenv/registered-definition? {} def-name)
      (do
        ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition as axiom: " def-name)))
    (let [definition (d/handle-axiom-declaration def-name {} params ty)
          quoted-def# definition]
      `(do
         (def ~def-name ~quoted-def#)
         (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                       :doc (mk-doc "Axiom" (quote ~ty) ~doc)
                                                       :arglists (list (quote ~params)))))
         [:declared :axiom (quote ~def-name)]))))


;;{
;; ## Notations
;;}

(defn parse-notation-args [def-name def-doc def-params def-body]
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

(defn parse-special-args [def-name def-doc def-params def-body]
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

By convention, all specials begin with a percent character, cf. e.g. [[%type-of]].

Remark: specials are generally used to simplify proofs, but should be used with care
since they are arbitrary functions. The risk is limited, though, since they cannot 
  introduce inconsistencies, and may at worst generate a looping behavior."
  [def-name def-doc def-params & def-body]
  (parse-special-args def-name def-doc def-params def-body)
  (when (defenv/registered-definition? {} def-name)
    (do
      ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition as special: " def-name)))
  `(do
     (def ~def-name (defenv/->Special (quote ~def-name) ~(- (count def-params) 2)
                      (fn ~def-params (do ~@def-body))))
     (alter-meta! (var ~def-name)  (fn [m#] (assoc m#
                                                   :doc ~def-doc
                                                   :arglists (list (quote ~(vec (rest (rest def-params))))))))
     [:defined :special (quote ~def-name)]))

(defspecial %type-of
  "A special operator such that an occurrence of the
term `(%type-of term)` is replaced by the *type* of `term`."
  [def-env ctx term]
  (let [[status ty] (ty/type-of-term def-env ctx term)]
    (if (= status :ko)
      (throw (ex-info "Cannot synthetize type of term" {:special 'latte.core/%type-of :term term :from ty}))
      ty)))

;; (example
;;  ((:special-fn %type-of) {} '[[x ✳]] 'x)
;;  => ✳)
 

;;{
;; ## Top-level term parsing
;;}

(defn parse-context-args [def-env args]
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

(defmacro term [& args]
    (let [def-env {}
          t (stx/parse def-env (last args))
          ctx (parse-context-args def-env (butlast args))]
      ;; (println "[term] t = " t " ctx = " ctx)
      (if (latte.kernel.norm/beta-eq? def-env ctx t :kind)
        '□
        (let [ty (ty/type-of def-env ctx t)]
          (list 'quote t)))))

;;{
;; ## Top-level type checking
;;}

(defmacro type-of [& args]
  (let [def-env {}
        t (stx/parse def-env (last args))
        ctx (parse-context-args def-env (butlast args))]
    (let [ty (ty/type-of def-env ctx t)]
      (list 'quote ty))))

(defmacro check-type? [& args]
  (let [def-env {}
        t (stx/parse def-env (last (butlast args)))
        ty (stx/parse def-env (last args))
        ctx (parse-context-args def-env (butlast (butlast args)))]
    ;;(println "[check-type?] ctx=" ctx)
    (let [tty (ty/type-of def-env ctx t)]
      (n/beta-eq? def-env ctx ty tty))))

;;{
;; ## Top-level term equivalence
;;}

(defn === [t1 t2]
  (let [def-env {}
        t1 (stx/parse def-env t1)
        t2 (stx/parse def-env t2)]
    (n/beta-eq? def-env [] t1 t2)))

(def term= ===)

;;{
;; ## Proof handling
;;}

(defmacro try-proof
  "Tries (but does not register) a proof of theorem named `thm-name` using the given proof `method`
  and `steps`."
  [thm-name method & steps]
  (let [def-env {}
        [status thm] (defenv/fetch-definition def-env thm-name)]
    (if (= status :ko)
      [:ko {:msg "No such theorem." :name thm-name}]
      (let [[status proof-term]
            (p/check-proof def-env (reverse (:params thm)) (:type thm) method steps)]
        (if (= status :ko)
          [:ko {:msg (str "Proof failed: " (:msg proof-term))
                :theorem thm-name
                :error (dissoc proof-term :msg)}]
          `(do
             [:ok {:qed (quote ~thm-name)}]))))))

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
    (let [[status proof-term]
          (p/check-proof def-env (reverse (:params thm)) (:type thm) method steps)]
      (if (= status :ko)
        (throw (ex-info (str "Proof failed: " (:msg proof-term)) {:theorem thm-name
                                                                  :error (dissoc proof-term :msg)}))
        (let [new-thm (assoc thm :proof proof-term)]
          ;;(println "HERE" "HERE" "HERE")
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

Implication is right arrociative:

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
