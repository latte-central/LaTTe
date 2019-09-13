(ns latte.utils
  "Misc. utilities for LaTTe libraries."
  (:require [clojure.string :as str]
            [clojure.walk :as w]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.norm :as norm]))


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

;;; ===================================================
;;; Handling of implicit type parameters (?T, ?U, etc.)
;;; ===================================================

(defn implicit-type-parameter? [v]
  (and (symbol? v)
       (= (first (name v)) \?)))

;; (implicit-type-parameter? 'x) => false
;;(implicit-type-parameter? '?x) => true
;;(implicit-type-parameter? '???x) => true

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
  (let [+itypes+ (atom (sorted-set))
        params' (w/postwalk (fn [x]
                              (if (implicit-type-parameter? x)
                                (do (swap! +itypes+ (fn [tys] (conj tys (explicit-type-name x))))
                                    (explicit-type-name x))
                                x)) params)]
    (if (empty? @+itypes+)
      nil
      {:implicit-types @+itypes+
       :new-params (into [] (concat (map (fn [ty] [(explicit-type-name ty) :type]) @+itypes+)
                                    params'))
       })))

;; (fetch-implicit-type-parameters '[[T :type] [U :type] [R (rel T U)]])
;; => nil

;; (fetch-implicit-type-parameters '[[U :type] [R (rel ?T U)]])
;; => {:implicit-types #{T}, :new-params [[T :type] [U :type] [R (rel T U)]]}

;; (fetch-implicit-type-parameters '[[R (rel ?T ?U)]])
;; => {:implicit-types #{T U}, :new-params [[T :type] [U :type] [R (rel T U)]]}

(defonce +implicit-type-parameters-handlers+ (atom {}))

(defn register-implicit-type-parameters-handler!
  [keysym handler-fn arity]
  (swap! +implicit-type-parameters-handlers+ (fn [old] (assoc old keysym [handler-fn arity]))))

(defn fetch-implicit-type-parameter-handler
  ([implicit-types def-env-var ctx-var [param-var param-ty]]
   (fetch-implicit-type-parameter-handler @+implicit-type-parameters-handlers+ implicit-types def-env-var ctx-var param-var param-ty))
  ([handlers implicit-types def-env-var ctx-var param-var param-ty]
   (if-let [[handler-fn arity] 
            (and (sequential? param-ty)
                 (>= (count param-ty) 1)
                 (get handlers (first param-ty)))]
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
     [implicit-types nil])))


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
