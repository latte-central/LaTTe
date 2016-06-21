(ns latte.core
  (:require [latte.presyntax :as stx]))

(defn latte-definition? [v]
  (and (map? v)
       (contains? v :tag)
       (contains? #{::term ::theorem ::axiom} (:tag v))))

(defn build-initial-definition-environment!
  []
  (let [ns-env (ns-map *ns*)]
    ;; (if (contains? ns-env '+latte-definition-environment+)
    ;;   (throw (ex-info "Cannot build initial definition environment: already existing" {:namespace (namespace '+latte-definition-environment+)
    ;;                                                                                    :var '+latte-definition-environment+}))
    (intern (ns-name *ns*) '+latte-definition-environment+
            (atom (reduce (fn [def-env [name definition]]
                            ;; (print "name = " name "def = " definition)
                            (if (latte-definition? definition)
                              (do (print "name = " name "def = " definition)
                                  (println " (... latte definition registered ...)")
                                  (assoc def-env name definition))
                              (do ;; (println " (... not a latte definition ...)")
                                def-env))) {} ns-env)))))
;;)

(defn fetch-def-env-atom
  []
  (let [lvar (let [lv (resolve '+latte-definition-environment+)]
               (if (not lv)
                 (do (build-initial-definition-environment!)
                     (resolve '+latte-definition-environment+))
                 lv))]
    ;;(println "Resolved!" lvar)
    @lvar))


(defn fetch-definition-environment
  []
  @(fetch-def-env-atom))

(defn handle-term-name [tdef name]
  (if (not (symbol? name))
    (throw (ex-info "Term name must be a symbol" {:name name}))
    (assoc tdef :name name)))

(defn handle-term-documentation [tdef doc]
  (if (not (string? doc))
    (throw (ex-info "Term documentation must be a string." {:doc doc}))
    (assoc tdef :doc doc)))

(defn handle-term-definition [tdef def-env params body]
  (let [params (mapv (fn [[x ty]] [x (stx/parse def-env ty)]) params)
        body (stx/parse def-env body)]
    ;; TODO : type checking
    (assoc tdef
           :params params
           :arity (count params)
           :parsed-term body)))

(defn register-term-definition! [name definition]
   (let [def-atom (fetch-def-env-atom)]
     (swap! def-atom (fn [def-env]
                       (assoc def-env name definition)))))

(defmacro defterm
  [name doc params body]
  ;;(println "name =" name " doc =" doc " params =" params " body =" body)
  (let [def-env (fetch-definition-environment)]
    ;;(println "def env = " def-env)
    (do
      (when (contains? def-env name)
        ;;(throw (ex-info "Cannot redefine term." {:name name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition of term: " name))
      (let [definition (as-> {:tag ::term} $
                         (handle-term-name $ name)
                         (handle-term-documentation $ doc)
                         (handle-term-definition $ def-env params body))
            quoted-def (list 'quote definition)]
        (register-term-definition! name definition)
        `(do
           (def ~name ~quoted-def)
           [:resistered ~name])))))



