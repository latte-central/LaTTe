(ns latte.script
  "Declarative proof scripts."

  (:require [clj-by.example :refer [example do-for-example]])

  (:require [latte.utils :as u])
  (:require [latte.presyntax :as stx])
  (:require [latte.typing :as ty :refer [type-of-term]])
  (:require [latte.core :as core])

  )

(def ^:private +examples-enabled+)

(defn do-assume [def-env ctx x ty]
  (if (or (not (symbol? x)) (stx/reserved-symbol? x))
    [:ko {:msg "Not a correct variable in assume step." :provided x}]
    (let [[status ty] (stx/parse-term def-env ty)]
      (if (= status :ko)
        [:ko {:msg "Parse error in assume step" :error ty}]
        (if-not (ty/proper-type? def-env ctx ty)
          [:ko {:msg "Not a proper type in assume step" :term ty}]
          [:ok [def-env (u/vcons [x ty] ctx)]])))))  ;; XXX: ctx should be a seq ?

(example
 (do-assume '{test :nothing}
            '[[A ✳]]
            'x 'A)
 => '[:ok [{test :nothing} [[x A] [A ✳]]]])

(example
 (do-assume '{test :nothing}
            '[[x A] [A ✳]]
            'y 'x)
 => '[:ko {:msg "Not a proper type in assume step", :term x}])

(defn undo-assume [def-env ctx x]
  (if (not= (ffirst ctx) x)
    [:ko {:msg "Cannot undo assume: variable not in head of context." :variable x}]
    [:ok [def-env (rest ctx)]]))

(example
 (undo-assume '{test :nothing}
              '[[x A] [A ✳]]
              'x)
 => '[:ok [{test :nothing} ([A ✳])]])

(example
 (undo-assume '{test :nothing}
              '[[A ✳] [x A]]
              'x)
 => '[:ko {:msg "Cannot undo assume: variable not in head of context.",
           :variable x}])

(defn do-have [def-env ctx name params have-type method have-arg]
  (let [[status term] (case method
                        (:by :term) (stx/parse-term def-env have-arg)
                        (:from :abst :abstr)
                        (if-not (and (vector? have-arg)
                                     (= (count have-arg) 2))
                          [:ko {:msg "Cannot perform have step: argument is not of the form [var term]"
                                :have-arg have-arg}]
                          (if-let [ty (ty/env-fetch ctx (first have-arg))]
                            (stx/parse-term def-env (list 'lambda [(first have-arg) ty] (second have-arg)))
                            [:ko {:msg "No such variable in context" :variable (first have-arg)}]))
                        
                        (throw (ex-info "No such method for proof script." {:have-name name :method method})))]
    (if (= status :ko)
      [:ko {:msg "Cannot perform have step: incorrect term." :have-name name :from term}]
      (let [[status have-type] (stx/parse-term def-env have-type)]
        (if (= status :ko)
          [:ko {:msg "Cannot perform have step: incorrect type." :habe-name name :from have-type}]
          (if-not (ty/type-check? def-env ctx term have-type)
            [:ko {:msg "Cannot perform have step: synthetized term and type do not match."
                  :have-name name
                  :term term :type have-type}]
            (if (nil? name)
              [:ok [def-env ctx]]
              (let [[status tdef] (core/handle-term-definition
                                   {:tag ::core/defterm :name name :doc "<have step>"}
                                   def-env
                                   ctx
                                   params
                                   term)]
                (if (= status :ko)
                  [:ko {:msg "Cannot perform have step: wrong local definition."
                        :have-name name
                        :from tdef}]
                  [:ok [(assoc def-env name tdef) ctx]])))))))))

(example
 (do-have {}
          '[[A ✳] [x A]]
          'step [] 'A :by 'x)
 => '[:ok [{step {:tag :latte.core/defterm,
                  :name step, :doc "<have step>", :params [], :arity 0,
                  :type A, :parsed-term x}}
           [[A ✳] [x A]]]])

(defn undo-have [def-env ctx name]
  (if-not (contains? def-env name)
    [:ko {:msg "Cannot undo have step: unknown local definition."
          :have-name name}]
    [:ok (dissoc def-env name) ctx]))

