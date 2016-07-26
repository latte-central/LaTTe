(ns latte.kernel.defenv
  "The definitional environment."

  )

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
