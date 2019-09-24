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
  (let [[def-Descr def-descr def-name-kw] (case def-kind
                                            :definition ["Definition" "definition" :def-name]
                                            :theorem ["Theorem" "theorem" :thm-name]
                                            :lemma ["Lemma" "lemma" :lem-name]
                                            :axiom ["Axiom" "axiom" :ax-name]
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
               {def-name-kw def-name
                :nb-args (count args)}]
              (let [params (if def-doc
                             (nth args 2)
                             (second args))
                    [status def-params infos] (parse-def-params params)]
                (if (= status :ko)
                  [:ko "Cannot parse parameter list" {def-name-kw def-name
                                                      :from (assoc infos :msg def-params)}]
                  (if (or (and def-doc (> (count args) 4))
                          (and (nil? def-doc) (> (count args) 3)))
                    [:ko (str "Too many arguments for " def-descr ".")  {def-name-kw def-name
                                                                         :nb-args (count args)
                                                                         :garbage (drop 4 args)}]
                    ;; everything's fine
                    [:ok "" {def-name-kw def-name
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
              (not= (count param) 2)
              [:ko "Parameter must be a pair `[name type]`." {:param param}]
              (not= (symbol? (first param)))
              [:ko "Parameter name must be a symbol." {:param param}]
              :else
              (recur (rest params) nil (conj def-params param))))
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




               




