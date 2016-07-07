(ns latte.kernel.defenv
  "The definitional environment."
  )

;;{
;; ## Definitional environment
;;}

(defn latte-definition? [v]
  (and (map? v)
       (contains? v :tag)
       (contains? #{:term :theorem :axiom} (:tag v))))


(defn fetch-definition [locals sym]
  ;;(println "[fetch-definition] locals=" locals "sym=" sym)
  (if-let [ldef (get locals sym)]
    [:ok ldef]
    (if-let [rgdef (resolve sym)]
      (let [gdef @rgdef]
        ;; (println "[fetch-definition] " gdef)
        (if (latte-definition? gdef)
          [:ok gdef]
          [:ko {:msg "Not a LaTTe definition" :def sym}]))
      [:ko {:msg "No such definition" :def sym}])))

(defn registered-definition? [locals sym]
  (let [[status _] (fetch-definition locals sym)]
    (= status :ok)))
