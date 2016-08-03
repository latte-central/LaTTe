(ns latte.kernel.proof
  "Declarative proof handling."

  (:require [clojure.set :as set])

  (:require [clj-by.example :refer [example do-for-example]])

  (:require [latte.kernel.utils :as u])

  (:require [latte.kernel.defenv :as defenv])
  (:require [latte.kernel.presyntax :as stx])
  (:require [latte.kernel.syntax :refer [free-vars]])
  (:require [latte.kernel.typing :as ty :refer [type-of-term]])
  (:require [latte.kernel.norm :as n])
  (:require [latte.kernel.defs :as d])

  )

(def ^:private +examples-enabled+)

;;{
;; # Proof top-level form
;;}


(declare evaluate-script)

(defn check-proof-term [def-env ctx thm-ty proof-term]
  ;; (println "[check-proof-term] def-env=" def-env "ctx=" ctx "thm-ty=" thm-ty "proof-term=" proof-term)
  (let [[status proof] (stx/parse-term def-env proof-term)]
    (if (= status :ko)
      [:ko {:msg (str "wrong proof term,  " (:msg proof))
            :error (dissoc proof :msg)}]
      (let [[status ptype] (ty/type-of-term def-env ctx proof)]
        ;; (println "[check-proof-term] type-of-proof=" ptype)
        (if (= status :ko)
          [:ko {:msg (str "type error, " (:msg ptype))
                :error (dissoc ptype :msg)}]
          (if (not (n/beta-eq? def-env ctx thm-ty ptype))
            [:ko {:msg "proof checking error (type mismatch)"
                  :expected-type thm-ty
                  :proof-type ptype}]
            [:ok proof]))))))

(defn check-proof
  [def-env ctx thm-ty method steps]
  (let [[status proof-term]
        (case method
          :term (cond
                  (empty? steps)
                  [:ko {:msg "missing proof term" :steps steps}]
                  (seq (rest steps))
                  [:ko {:msg "too many proof steps, direct method requires a single term" :steps steps}]
                  :else
                  [:ok (first steps)])
          :script (evaluate-script steps def-env ctx def-env ctx '())
          [:ko {:msg "no such proof method" :method method}])]
    (if (= status :ko)
      [:ko proof-term]
      (check-proof-term def-env ctx thm-ty proof-term))))

;;{
;; # Declarative proofs
;;}

(defn parse-assume-step [script]
  (cond
    (< (count script) 3)
    [:ko {:msg "Wrong assume step: at least 2 arguments needed" :nb-args (dec (count script))}]
    (not (>= (count (second script)) 2))
    [:ko {:msg "Wrong assume step: at least one variable/type binding required." :bindings (second script)}]
    :else
    (let [[x ty & rst] (second script)
          body (rest (rest script))]
        (if (seq rst)
          [:ok {:binding [x ty] :body (list 'assume (vec rst) body)}]
          [:ok {:binding [x ty] :body body}]))))

(example
 (parse-assume-step '(assume [x :type] body))
 => '[:ok {:binding [x :type], :body (body)}])

(example
 (parse-assume-step '(assume [A :type x A] body))
 => '[:ok {:binding [A :type], :body (assume [x A] (body))}])

(defn do-assume-step [def-env ctx x ty]
  (if (or (not (symbol? x)) (stx/reserved-symbol? x))
    [:ko {:msg "Not a correct variable in assume step." :provided x}]
    (let [[status ty] (stx/parse-term def-env ty)]
      (if (= status :ko)
        [:ko {:msg "Parse error in assume step" :error ty}]
        (if-not (ty/proper-type? def-env ctx ty)
          [:ko {:msg "Not a proper type in assume step" :term ty}]
          [:ok [def-env (u/vcons [x ty] ctx)]])))))  ;; XXX: ctx should be a seq ?

(example
 (do-assume-step '{test :nothing}
            '[[A ✳]]
            'x 'A)
 => '[:ok [{test :nothing} [[x A] [A ✳]]]])

(example
 (do-assume-step '{test :nothing}
            '[[x A] [A ✳]]
            'y 'x)
 => '[:ko {:msg "Not a proper type in assume step", :term x}])

(defn undo-assume-step [def-env ctx x]
  (if (not= (ffirst ctx) x)
    [:ko {:msg "Cannot undo assume: variable not in head of context." :variable x}]
    [:ok [def-env (rest ctx)]]))

(example
 (undo-assume-step '{test :nothing}
              '[[x A] [A ✳]]
              'x)
 => '[:ok [{test :nothing} ([A ✳])]])

(example
 (undo-assume-step '{test :nothing}
              '[[A ✳] [x A]]
              'x)
 => '[:ko {:msg "Cannot undo assume: variable not in head of context.",
           :variable x}])


;; have-step syntax :
;;
;; (have step params ty method arg)
;; (have step ty method arg)
;; (have ty method arg)


(defn parse-have-name [have-name]
  (let [[status have-name] (cond
                             (symbol? have-name) [:ok have-name]
                             (and (sequential? have-name)
                                  (seq have-name)
                                  (empty? (rest have-name))
                                  (symbol? (first have-name))) [:ok (first have-name)]
                             :else
                             [:ko {:msg "wrong name" :name have-name}])]
    (if (= status :ko)
      [:ko have-name]
      (if (stx/reserved-symbol? have-name)
        [:ko {:msg "name is reserved" :name have-name}]
        [:ok have-name]))))

(defn parse-have-step [script]
  (case (count script)
    4 (let [[ty meth arg] (rest script)]
        [:ok {:have-name nil, :params [],
              :have-type ty, :method meth, :have-arg arg}])
    5 (let [[step ty meth arg] (rest script)
            [status have-name] (parse-have-name step)]
        (if (= status :ko)
          [:ko have-name]
          [:ok {:have-name have-name, :params [],
                :have-type ty, :method meth, :have-arg arg}]))
    6 (let [[step params ty meth arg] (rest script)
            [status have-name] (parse-have-name step)]
        (if (= status :ko)
          [:ko have-name]
          [:ok {:have-name have-name, :params params,
                :have-type ty, :method meth, :have-arg arg}]))
    [:ko {:msg "Wrong have step:  3, 4 or 5 arguments needed" :nb-args (dec (count script))}]))

(reverse (butlast [1 2 3 4]))

(defn prepare-discharge [ctx vars term]
  (if (seq vars)
    (if-let [ty (ty/ctx-fetch ctx (first vars))]
      (recur ctx (rest vars) (list 'lambda [(first vars) ty] term))
      [:ko {:msg "No such variable in context" :variable (first vars)}])
    [:ok term]))

(defn do-have-step [def-env ctx name params have-type method have-arg]
  ;;(println "[do-have-step] name=" name "have-arg=" have-arg)
  ;;(println "   ctx=" ctx)
  (let [[status term]
        (case method
          (:by :term) (stx/parse-term def-env have-arg)
          (:from :abst :abstr :discharge)
          (if-not (and (vector? have-arg)
                       (>= (count have-arg) 2))
            [:ko {:msg "Cannot perform have step: argument is not of the form [var ... var term]"
                  :have-arg have-arg}]
            (let [[status term] (prepare-discharge ctx (reverse (butlast have-arg)) (last have-arg))]
              (if (= status :ko)
                [:ko term]
                (stx/parse-term def-env term))))
          ;; else
          [:ko {:msg "No such method for proof script." :have-name name :method method}])]
    ;; check synthetized term
    (if (= status :ko)
      [:ko {:msg "Cannot perform have step: incorrect term." :have-name name :from term}]
      (let [term (n/special-normalize def-env ctx term)
            [status have-type] (if (and (symbol? have-type)
                                        (= (clojure.core/name have-type) "_"))
                                 [:ok nil]
                                 (stx/parse-term def-env have-type))]
        (if (= status :ko)
          [:ko {:msg "Cannot perform have step: type mismatch." :have-name name :from have-type}]
          (let [[status have-type]
                (if (nil? have-type)
                  (let [[status have-type] (ty/type-of-term def-env ctx term)]
                    (if (= status :ko)
                      [:ko (assoc (dissoc have-type :msg)
                                  :msg (str "Cannot perform have step: " (:msg have-type)))]
                      [:ok have-type]))
                  (let [res (ty/type-check? def-env ctx term have-type)]
                    (if-not res
                      [:ko {:msg "Cannot perform have step: synthetized term and type do not match."
                            :have-name name
                            :term term :type have-type}]
                      [:ok have-type])))]
            (cond (= status :ko) [:ko have-type]
                  (nil? name) [:ok [def-env ctx]]
                  :else
                  (let [[status tdef] (d/handle-term-definition
                                       name
                                       def-env
                                       ctx
                                       params
                                       term
                                       have-type)]
                    ;;(println "[have-step] term=" term)
                    ;;(println "            def=" (:parsed-term tdef))
                    (if (= status :ko)
                      [:ko {:msg "Cannot perform have step: wrong local definition."
                            :have-name name
                            :from tdef}]
                      [:ok [(assoc def-env name tdef) ctx]])))))))))

(example
 (do-have-step {}
          '[[A ✳] [x A]]
          'step [] 'A :by 'x)
 => '[:ok [{step #latte.kernel.defenv.Definition{:name step, :params [], :arity 0, :parsed-term x, :type A}} [[A ✳] [x A]]]])

(example
 (let [{name :have-name params :params have-type :have-type method :method have-arg :have-arg}
       (second (parse-have-step '(have step A :by x)))]
   (do-have-step {} '[[A ✳] [x A]] name params have-type method have-arg))
 => '[:ok [{step #latte.kernel.defenv.Definition{:name step, :params [], :arity 0, :parsed-term x, :type A}}
           [[A ✳] [x A]]]])

(defn do-qed-step [start-def-env end-def-env start-ctx end-ctx term]
  (let [[status term] (stx/parse-term end-def-env term)]
    (if (= status :ko)
      [:ko {:msg "Cannot do QED step: parse error." :error term}]
      (let [delta-env (select-keys end-def-env (set/difference (set (keys end-def-env))
                                                                (set (keys start-def-env))))
            term' (n/delta-normalize-local delta-env term)
            fv (free-vars term')
            count-start-ctx (count start-ctx)]
        ;;(println "[do-qed-step] delta-env=" (keys delta-env))
        ;;(println "    term = " term)
        ;;(println "    term' = " term')
        (loop [delta-ctx end-ctx, count-delta-ctx (count end-ctx), term term']
          (if (> count-delta-ctx count-start-ctx)
            (let [[x ty] (first delta-ctx)]
              (if (contains? fv x)
                (recur (rest delta-ctx) (dec count-delta-ctx) (list 'lambda [x ty] term))
                (recur (rest delta-ctx) (dec count-delta-ctx) term)))
            (do ;;(println "[qed]")
                ;;(println "-----------------------------------------")
                ;;(clojure.pprint/pprint term)
                ;;(println "-----------------------------------------")
                [:ok term])))))))


(defn do-showdef-step [def-env arg]
  (println "[showdef]" arg)
  (let [[status sdef] (defenv/fetch-definition def-env arg)]
    (if (= status :ok)
      (if (defenv/latte-definition? sdef)
        (do
          (println "-----------------------------------------")
          (clojure.pprint/pprint sdef)
          (println "-----------------------------------------"))
        (println "  ==> not a LaTTe definition"))
      (println "  ==> no such definition"))))

(defn do-showterm-step [def-env ctx arg]
  (println "[showterm]" arg)
  ;;(println "def-env:")
  ;;(clojure.pprint/pprint def-env)
  (println "-----------------------------------------")
  (let [[status term] (stx/parse-term def-env arg)]
    ;; (println "[showterm] parsed=" term)
    (if (= status :ko)
      (clojure.pprint/pprint term)
      (let [term (n/normalize def-env ctx term)]
        (clojure.pprint/pprint term)
        (let [[status ty] (ty/type-of-term def-env ctx term)] 
          (if (= status :ko)
            (clojure.pprint/pprint ty)
            (do (print "::")
                (clojure.pprint/pprint ty)))))))
  (println "-----------------------------------------"))

(defn do-showctx-step [def-env ctx]
  (println "[showctx]")
  (println "-----------------------------------------")
  (clojure.pprint/pprint ctx)
  (println "-----------------------------------------"))

(defn evaluate-script [script start-def-env start-ctx def-env ctx cont-stack]
  ;; (println "[evaluate-script] ctx=" ctx)
  ;; (println "---------------------------------------------")
  ;; (clojure.pprint/pprint script)
  ;; (println "---------------------------------------------")
  (if (seq script)
    (if (sequential? (first script))
      (recur (first script) start-def-env start-ctx def-env ctx (conj cont-stack (rest script)))
      (if (string? (first script))
        ;; strings are used for comments inside proof scripts
        (recur (rest script) start-def-env start-ctx def-env ctx cont-stack)
        (case (first script)
          assume
          (let [[status info] (parse-assume-step script)]
            (if (= status :ko)
              [:ko info]
              (let [{[x ty] :binding body :body} info]
                (let [[status res] (do-assume-step def-env ctx x ty)]
                  (if (= status :ko)
                    [:ko res]
                    (recur body start-def-env start-ctx
                           (first res) (second res) (conj cont-stack (list 'undo-assume-step x))))))))
          undo-assume-step
          (let [[status res] (undo-assume-step def-env ctx (second script))]
            (if (= status :ko)
              [:ko res]
              (recur '() start-def-env start-ctx (first res) (second res) cont-stack)))
          have
          (let [[status info] (parse-have-step script)]
            (if (= status :ko)
              [:ko info]
              (let [{have-name :have-name params :params
                     have-type :have-type method :method have-arg :have-arg} info]
                (let [[status res] (do-have-step def-env ctx have-name params have-type method have-arg)]
                  (if (= status :ko)
                    [:ko res]
                    (recur '() start-def-env start-ctx (first res) (second res) cont-stack))))))
          qed
          (do-qed-step start-def-env def-env start-ctx ctx (second script))
          showdef
          (do (do-showdef-step def-env (second script))
              (recur '() start-def-env start-ctx def-env ctx cont-stack))
          showterm
          (do (do-showterm-step def-env ctx (second script))
              (recur '() start-def-env start-ctx def-env ctx cont-stack))
          showctx
          (do (do-showctx-step def-env ctx)
              (recur '() start-def-env start-ctx def-env ctx cont-stack))
          ;; else
          (throw (ex-info "Cannot evaluate script" {:script script})))))
    ;; at end of script
    (if (seq cont-stack)
      (recur (first cont-stack) start-def-env start-ctx def-env ctx (rest cont-stack))
      [:ko {:msg "Missing `qed` step in proof."}])))
