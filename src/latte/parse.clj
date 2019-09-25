;;{
;; # Parsing tools
;;
;; In this namespace all the user-facing syntactic artefacts of LaTTe
;; are checked for well-formedness. This is not concerned with term-level parsing.
;; The emphasis is on precision and clarity of (potential) error messages
;;}

(ns latte.parse
  )

(declare check-def-name
         parse-def-params)

(defn parse-definition [def-kind args]
  (let [[def-Descr def-descr] (case def-kind
                                :definition ["Definition" "definition"]
                                :theorem ["Theorem" "theorem"]
                                :lemma ["Lemma" "lemma"]
                                :axiom ["Axiom" "axiom"]
                                (throw (ex-info "No such definition kind." {:def-kind def-kind})))]
    (if (< (count args) 3)
      [:ko (str def-Descr " form requires at least 3 arguments.") {:nb-args (count args)}]
      (let [def-name (first args)
            [status msg infos] (check-def-name def-name)]
        (if (= status :ko)
          [status msg infos]
          (let [def-doc (if (string? (second args))
                          (second args)
                          nil)]
            (if (and def-doc
                     (< (count args) 4))
              [:ko (str def-Descr " form (with docstring) requires at least 4 arguments.") 
               {:name def-name
                :nb-args (count args)}]
              (let [params (if def-doc
                             (nth args 2)
                             (second args))
                    [status def-params infos] (parse-def-params params)]
                (if (= status :ko)
                  [:ko "Cannot parse parameter list" {:name def-name
                                                      :from (assoc infos :msg def-params)}]
                  (if (or (and def-doc (> (count args) 4))
                          (and (nil? def-doc) (> (count args) 3)))
                    [:ko (str "Too many arguments for " def-descr ".")  {:name def-name
                                                                         :nb-args (count args)
                                                                         :garbage (drop 4 args)}]
                    ;; everything's fine
                    [:ok "" {:name def-name
                             :doc def-doc
                             :params def-params
                             :body (if def-doc
                                     (nth args 3)
                                     (nth args 2))}]))))))))))

(defn check-def-name [name]
  (if (symbol? name)
    [:ok name nil]
    [:ko "Definition name must be a symbol." {:name name}]))

(defn parse-def-params [params]
  (if (not (vector? params))
    [:ko "Parameters must be specifed as a vector." {:params params}]
    (loop [params params, pname nil, def-params []]
      (if (seq params)
        (cond
          (vector? (first params))
          (let [param (first params)]
            (cond
              (not (nil? pname)) 
              [:ko "Expecting a parameter type, not a pair." {:param-name pname
                                                              :param-type param}]
              (< (count param) 2)
              [:ko "Wrong parameter syntax." {:param param}]
              :else
              (let [ptype (last param)
                    [status msg res]
                    (loop [names (butlast param), nparams def-params]
                      (if (seq names)
                        (if (not (symbol? (first names)))
                          [:ko "Parameter name must be a symbol." {:param param
                                                                   :name (first names)}]
                          (recur (rest names) (conj nparams [(first names) ptype])))
                        ;; no more names
                        [:ok "" nparams]))]
                (if (= status :ko)
                  [:ko msg res]
                  (recur (rest params) nil res)))))
          ;; a non-vector parameter
          (nil? pname)
          (if (not (symbol? (first params)))
            [:ko "Expecting a parameter name as a symbol." {:param (first params)}]
            (recur (rest params) (first params) def-params))
          :else ;; type part
          (recur (rest params) nil (conj def-params [pname (first params)])))
        ;; no more parameters
        (if (not (nil? pname))
          [:ko "Parameter is without a type." {:param-name pname}]
          [:ok def-params nil])))))




               




