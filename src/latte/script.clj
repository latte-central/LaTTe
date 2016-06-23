(ns latte.script
  "Declarative proof scripts."

  (:require [latte.utils :as u])
  (:require [latte.presyntax :as stx])
  (:require [latte.typing :as ty :refer [type-of-term]])
  (:require [latte.core :as core])
  )


(defn do-assume [def-env ctx x ty]
  (if (or (not (symbol? x)) (stx/reserved-symbol? x))
    [:ko {:msg "Not a correct variable in assume step." :provided x}]
    (let [[status ty] (stx/parse-term def-env ty)]
      (if (= status :ko)
        [:ko {:msg "Parse error in assume step" :error ty}]
        (if-not (ty/proper-type? def-env ctx ty)
          [:ko {:msg "Not a property type in assume step" :term ty}]
          [:ok [def-env (u/vcons [x ty] ctx)]])))))  ;; XXX: ctx should be a seq ?

(defn undo-assume [def-env ctx x ty]
  (if (not= (ffirst ctx) x)
    [:ko {:msg "Cannot undo assume: variable not in head of context." :variable x}]
    [:ok [def-env (rest ctx)]]))


(defn do-have [def-env ctx name params have-type method have-arg]
  (let [[status term] (case method
                        :by (stx/parse-term def-env have-arg)
                        :appl (throw (ex-info "Method :appl not yet enabled for proof scripts."))
                        :abstr (throw (ex-info "Method :abstr not yet enabled for proof scripts."))
                        (throw (ex-info "No such method for proof script." {:have-name name :method method})))]
    (if (= status :ko)
      [:ko {:msg "Cannot perform have step: incorrect term." :have-name name :reason term}]
      (let [[status have-type] (stx/parse-term def-env have-type)]
        (if (= status :ko)
          [:ko {:msg "Cannot perform have step: incorrect type." :habe-name name :reason have-type}]
          (if-not (ty/type-check? def-env ctx term have-type)
            [:ko {:msg "Cannot perform have step: synthetized term and type do not match."
                  :have-name name
                  :term term :type have-type}]
            (let [[status tdef] (core/handle-term-definition
                                 {:tag ::core/defterm :name name :doc "<have step>"}
                                 def-env
                                 params
                                 term)]
              (if (= status :ko)
                [:ko {:msg "Cannot perform have step: wrong local definition."
                      :have-name name
                      :raeson tdef}]
                [:ok [(assoc def-env name tdef) ctx]]))))))))

(defn undo-have [def-env ctx name]
  (if-not (contains? def-env name)
    [:ko {:msg "Cannot undo have step: unknown local definition."
          :have-name name}]
    [:ok (dissoc def-env name) ctx]))

