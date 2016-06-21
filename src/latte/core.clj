(ns latte.core
  (:require [latte.presyntax :as stx])
  (:require [latte.typing :as ty])
  )

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
    ;; (println "[handle-term-definition] def-env = " def-env " params = " params " body = " body)
    (let [[status ty] (ty/type-of-term def-env params body)]
      (if (= status :ko)
        (throw (ex-info "Type error" {:def tdef
                                      :error ty}))
        (assoc tdef
               :params params
               :arity (count params)
               :type ty
               :parsed-term body)))))

(defn register-term-definition! [name definition]
   (let [def-atom (fetch-def-env-atom)]
     (swap! def-atom (fn [def-env]
                       (assoc def-env name definition)))))

(defmacro defterm
  [def-name doc params body]
  ;;(println "def-name =" def-name " doc =" doc " params =" params " body =" body)
  (let [def-env (fetch-definition-environment)]
    ;;(println "def env = " def-env)
    (do
      (when (contains? def-env def-name)
        ;;(throw (ex-info "Cannot redefine term." {:name def-name})))
        ;; TODO: maybe disallow redefining if type is changed ?
        ;;       otherwise only warn ?
        (println "[Warning] redefinition of term: " def-name))
      (let [definition (as-> {:tag ::term} $
                         (handle-term-name $ def-name)
                         (handle-term-documentation $ doc)
                         (handle-term-definition $ def-env params body))
            quoted-def (list 'quote definition)]
        (register-term-definition! def-name definition)
        (let [name# (name def-name)]
          `(do
             (def ~def-name ~quoted-def)
             [:registered ~name#]))))))


(defmacro term [t]
  (let [def-env (fetch-definition-environment)
        t (stx/parse def-env t)]
    (if (latte.norm/beta-eq? t :kind)
      [:kind :sort]
      (let [ty (ty/type-of def-env [] t)]
        [(list 'quote t) (list 'quote ty)]))))
