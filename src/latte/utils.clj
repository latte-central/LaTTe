(ns latte.utils
  "Misc. utilities for LaTTe libraries."
  (:require [clojure.string :as str]
            [clojure.walk :as w]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.norm :as norm]
            [latte-kernel.presyntax :as stx]
            [latte-kernel.typing :as ty]))


;; decomposer (rebindable) parameters
(def ^:dynamic *decomposer-performs-delta-steps* true)
(def ^:dynamic *decomposer-performs-norm* true)

(defn decomposer
  ([decompose-fn def-env ctx term] (decomposer decompose-fn def-env ctx term true true))
  ([decompose-fn def-env ctx term try-delta? try-norm?]
   (let [[status res]
         (try [:ok (decompose-fn term)]
              (catch Exception e
                [:ko e]))]
     (if (= status :ok)
       res
       (let [[term' rcount] (if (and *decomposer-performs-delta-steps* try-delta?)
                              (norm/delta-step def-env ctx term)
                              [term 0])]
         (if (pos? rcount)
           (recur decompose-fn def-env ctx term' false try-norm?)
           (if (and *decomposer-performs-norm* try-norm?)
             (let [term' (norm/normalize def-env ctx term)]
               (recur decompose-fn def-env ctx term' false false))
             (throw res))))))))


(defn set-opacity! [defvar flag]
  "Equality is most of the time handled in an opaque way, but it
is sometimes required to handle it transparently. This function
 should be used in this case."
  (alter-var-root defvar (fn [eq]
                           (update eq :opts (fn [opts] (assoc opts :opaque flag))))))


(defn fetch-ns-elements
  "Fetch the LaTTe elements in specified `ns` (or the current namespace by default)."
  ([] (fetch-ns-elements *ns*))
  ([ns] (let [defs (ns-map ns)
              ;; some cleanups
              defs (into {}
                         (filter #(and (not (clojure.string/starts-with? (str (second %)) "#'clojure."))
                                       (var? (second %))) defs))]
          (reduce (fn [elems [ename evar]]
                    (let [elem (var-get evar)]
                      (cond
                        (defenv/definition? elem)
                        (assoc-in elems [:definitions ename] elem)
                        (defenv/theorem? elem)
                        (assoc-in elems [:theorems ename] elem)
                        (defenv/axiom? elem)
                        (assoc-in elems [:axioms ename] elem)
                        (defenv/notation? elem)
                        (assoc-in elems [:notations ename] elem)
                        (defenv/implicit? elem)
                        (assoc-in elems [:implicits ename] elem)
                        :else elems)))
                  {:theorems {}
                   :definitions {}
                   :axioms {}
                   :notations {}
                   :implicits {}} defs))))

;; (fetch-ns-elements (the-ns 'latte-prelude.prop))

;;; ===================================================
;;; Handling of implicit type parameters (?T, ?U, etc.)
;;; ===================================================

(defn implicit-type-parameter? [v]
  (if-not (symbol? v)
    false
    (let [sname (name v)]
      (and (> (count sname) 1)
           (= (first sname) \?)))))

;; (implicit-type-parameter? 'x) => false
;; (implicit-type-parameter? '?x) => true
;; (implicit-type-parameter? '???x) => true
;; (implicit-type-parameter? '?) => false

(defn explicit-type-name 
  "Generates the explicit name of an implicit type `ty`."
  [ty]
  ;; remark: we remove all question marks
  (symbol (str/replace (str ty) #"(\?)" "")))


;; (explicit-type-name 'x) => 'x
;; (explicit-type-name '?x) => 'x
;; (explicit-type-name '???x) => 'x
;; (explicit-type-name '???x???y?z???) => 'xyz
;; ==> this is a little bit "too much" but question
;;     marks should be avoided in type names anyway

(defn fetch-implicit-type-parameters
  "Fetch the implicit parameters in the `params` (parameters) list."
  [params]
  (let [[implicit-types explicit-type-params rest-params _] 
        (reduce (fn [[itypes eparams rparams finished] [pname ptype]]
                  (if (implicit-type-parameter? pname)
                    (if finished
                      (throw (ex-info "Implicit parameters must be at the front of parameters list." {:param pname}))
                      (if (stx/type? ptype)
                        (let [ename (explicit-type-name pname)]
                          [(conj itypes ename) (conj eparams [ename ptype]) rparams finished])
                        (throw (ex-info "Implicit parameter must be a type." {:param pname
                                                                              :param-type ptype}))))
                    ;; not an implicit type parameter, we're finished (and checking for misplaced implicit type params)
                    [itypes eparams (conj rparams [pname ptype]) true]))
                [#{} [] [] false] params)]
    (if (empty? implicit-types)
      nil
      {:implicit-types implicit-types
       :explicit-type-params explicit-type-params
       :rest-params rest-params})))

;; (fetch-implicit-type-parameters '[[T :type] [U :type] [R (rel T U)]])
;; => nil

;; (fetch-implicit-type-parameters '[[?T :type] [U :type] [R (rel T U)]])
;; => {:implicit-types #{T}, :explicit-type-params [[T :type]], :rest-params [[U :type] [R (rel T U)]]}

;; (fetch-implicit-type-parameters '[[?T :type] [?U :type] [R (rel T U)]])
;; => {:implicit-types #{U T}, :explicit-type-params [[T :type] [U :type]], :rest-params [[R (rel T U)]]}

(defonce +implicit-type-parameters-handlers+ (atom {}))

(defn fully-qualified-symbol 
  ([sym] (fully-qualified-symbol *ns* sym))
  ([ns sym] (symbol (str (ns-name ns) "/" sym))))

;; (fully-qualified-symbol 'test)
;; => latte.utils/test

;; (fully-qualified-symbol (the-ns 'latte-kernel.norm) 'test)
;; => latte-kernel.norm/test

(defn register-implicit-type-parameters-handler!
  [keysym handler-fn arity]
  (swap! +implicit-type-parameters-handlers+ 
         (fn [old] (assoc old 
                          (or (resolve keysym)
                              keysym) [handler-fn arity]
                          ;; (fully-qualified-symbol keysym) [handler-fn arity]
                          ))))

(defn fetch-atomic-implicit-type-parameter
  [def-env ctx ty]
  ty
  #_(let [[status ty] (ty/type-of def-env ctx term)]
    (if (= status :ok)
      ty
      (throw (ex-info "Cannot fetch implicit type" {:term term
                                                    :cause ty}))))
  )

(defn fetch-implicit-type-parameter-handler
  ([implicit-types def-env-var ctx-var [param-var param-ty]]
   (fetch-implicit-type-parameter-handler @+implicit-type-parameters-handlers+ implicit-types def-env-var ctx-var param-var param-ty))
  ([handlers implicit-types def-env-var ctx-var param-var param-ty]
   ;; atomic type
   (if (and (symbol? param-ty)
            (contains? implicit-types param-ty))
     [(disj implicit-types param-ty) [param-ty (list `fetch-atomic-implicit-type-parameter def-env-var ctx-var param-var)]]
     ;; compound type
     (if-let [[handler-fn arity] 
            (and (sequential? param-ty)
                 (>= (count param-ty) 1)
                 (let [search-key (or (resolve (first param-ty))
                                      (first param-ty))]
                   (get handlers search-key)))]
     ;; we have a handler
     (let [[implicit-types' lt-params]
           (reduce (fn [[itypes ltparams] param]
                     (if (contains? itypes param)
                       [(disj itypes param) (conj ltparams param)]
                       [itypes (conj ltparams '_)])) [implicit-types []] (rest param-ty))
           lt-expr (list handler-fn def-env-var ctx-var param-var)]
       (when (and arity (not= (count lt-params) arity))
         (throw (ex-info "Wrong arity for implicit type parameter handling" {:expected-arity arity
                                                                             :parameter-type param-ty})))
       [implicit-types' (if (= implicit-types' implicit-types)
                          nil
                          [(if (= (count lt-params) 1)
                             (first lt-params)
                             lt-params)
                           lt-expr])])
     ;; we don't have a handler
     [implicit-types nil]))))


;; (fetch-implicit-type-parameter-handler
;;  {'rel ['fetch-rel-type 2]}
;;  '#{T}
;;  'def-env
;;  'ctx
;;  'R-term 'T)
;; => [#{} [T (latte.utils/fetch-atomic-implicit-type-parameter def-env ctx R-term)]]


;; (fetch-implicit-type-parameter-handler
;;  {'rel ['fetch-rel-type 2]}
;;  '#{T U}
;;  'def-env
;;  'ctx
;;  'R-term '(rel T U))
;; => [#{} [[T U] (fetch-rel-type def-env ctx R-term)]]

;; (fetch-implicit-type-parameter-handler
;;  {'rel ['fetch-rel-type 2]}
;;  '#{T}
;;  'def-env
;;  'ctx
;;  'R-term '(rel T U))
;; => [#{} [[T _] (fetch-rel-type def-env ctx R-term)]]

;; (fetch-implicit-type-parameter-handler
;;  {'rel ['fetch-rel-type 2]}
;;  '#{}
;;  'def-env
;;  'ctx
;;  'R-term '(rel T U))
;; => [#{} nil]

;; (fetch-implicit-type-parameter-handler
;;  {'rel ['fetch-rel-type 2]}
;;  '#{}
;;  'def-env
;;  'ctx
;;  'R-term '(rel T U V))
;; => Wrong arity for implicit type parameter handling
;;    {:expected-arity 2, :parameter-type (rel T U V)}

;; (fetch-implicit-type-parameter-handler
;;  {'set ['fetch-set-type 1]}
;;  '#{T}
;;  'def-env
;;  'ctx
;;  'R-term '(set T))
;; => [#{} [T (fetch-set-type def-env ctx R-term)]]
