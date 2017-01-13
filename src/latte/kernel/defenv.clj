(ns latte.kernel.defenv
  "The definitional environment."

  )

;;{
;; ## Definitional entities
;;}

(defrecord Definition [name params arity parsed-term type])

(defn definition? [v]
  (instance? Definition v))

(defrecord Theorem [name params arity type proof])

(defn theorem? [v]
  (instance? Theorem v))

(defrecord Axiom [name params arity type])

(defn axiom? [v]
  (instance? Axiom v))

(defrecord Notation [name notation-fn])

;; somewhat hacky but "safe"
(defn- mk-args [n]
  (vec (repeat n nil)))

;; courtesy of #whocaresanyway@stackoverflow
(defn- arg-count [f]
  (let [m (first (.getDeclaredMethods (class f)))
        p (.getParameterTypes m)]
    (alength p)))

(defn- dummy-call [f]
  (let [n (arg-count f)]
    (apply f (mk-args n))))

(defn get-notation-fn [f]
  (:notation-fn (dummy-call f)))

(defn notation? [v]
  (and (fn? v)
       (instance? Notation (dummy-call v))))

(defrecord Special [name special-fn])

(defn special? [v]
  (instance? Special v))


(defn latte-definition? [v]
  (or (definition? v)
      (theorem? v)
      (axiom? v)
      (notation? v)
      (special? v)))

;;{
;; ## Definitional environment
;;}

(defn fetch-definition [locals sym]
  ;; (println "[fetch-definition] sym=" sym "(type" (type sym) ")")
  (cond
    (symbol? sym) (if-let [ldef (get locals sym)]
                    [:ok ldef]
                    (if-let [symvar (resolve sym)]
                      (recur locals symvar)
                      [:ko {:msg "No such (local) definition" :def sym}]))
    (var? sym) (let [gdef @sym]
                 ;;(println "[fetch-definition] " gdef)
                 [:ok gdef])
    :else (throw (ex-info "Cannot fetch definition (please report)"
                          {:sym sym}))))

(defn registered-definition? [locals sym]
  (let [[status _] (fetch-definition locals sym)]
    (= status :ok)))

(defn qualify-def [locals sym]
  (if (var? sym)
    sym
    (do
      (when (not (symbol? sym))
        (throw (ex-info "Value to qualify should be a var or a symbol (please report)" {:sym sym :type (type sym)})))
      (if-let [_ (get locals sym)]
        sym
        (resolve sym)))))
