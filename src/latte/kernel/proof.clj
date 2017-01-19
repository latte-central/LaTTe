(ns latte.kernel.proof
  "Declarative proof handling."

  (:require [clojure.set :as set]
            [clj-by.example :refer [example do-for-example]]
            [latte.kernel.utils :as u]
            [latte.kernel.defenv :as defenv]
            [latte.kernel.presyntax :as stx]
            [latte.kernel.syntax :refer [free-vars]]
            [latte.kernel.typing :as ty :refer [type-of-term]]
            [latte.kernel.norm :as n]
            [latte.kernel.defs :as d]))

;;;;===================================================================
;;;;======================== UPDATED UNTIL HERE =======================
;;;;===================================================================


(def ^:private +examples-enabled+)

;; uncomment for timing
;; (def ^:private +timing-enabled+)

(defmacro timing [explain expr]
  (if-let [ex-var (find-var (symbol (str *ns*) "+timing-enabled+"))]
    (if (var-get ex-var)
      `(let [start-time# (u/nano-time)
             res# ~expr
             end-time# (u/nano-time)
             elapsed# (float (/ (- end-time# start-time#)
                                1000000))]
         (println ~explain (str "(" elapsed# " ms)"))
         res#)
      `~expr)
    `~expr))

(defmacro when-timing [expr]
  (when-let [ex-var (find-var (symbol (str *ns*) "+timing-enabled+"))]
    (when (var-get ex-var)
      `~expr)))

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
      (let [[status ptype] (timing "- infer proof type"
                                   (ty/type-of-term def-env ctx proof))]
        ;; (println "[check-proof-term] type-of-proof=" ptype)
        (if (= status :ko)
          [:ko {:msg (str "type error, " (:msg ptype))
                :error (dissoc ptype :msg)}]
          (if (not (timing "- check proof type against theorem type"
                           (n/beta-eq? def-env ctx thm-ty ptype)))
            [:ko {:msg "proof checking error (type mismatch)"
                  :expected-type thm-ty
                  :proof-type ptype}]
            (do
              (when-timing
                  (println "=================================================================="))
              [:ok proof])))))))

(defn check-proof
  [def-env ctx thm-name thm-ty method steps]
  (let [[status proof-term]
        (case method
          :term (cond
                  (empty? steps)
                  [:ko {:msg "missing proof term" :steps steps}]
                  (seq (rest steps))
                  [:ko {:msg "too many proof steps, direct method requires a single term" :steps steps}]
                  :else
                  [:ok (first steps)])
          :script (do
                    (when-timing
                        (println "=== Checking proof of theorem" thm-name "(timing enabled) ==="))
                    (evaluate-script steps def-env ctx [] '()))
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

(defn do-assume-step [def-env ctx deps x ty]
  (cond
    (not (symbol? x))
    [:ko {:msg "Assume variable must be a symbol." :var-arg x}]
    (stx/reserved-symbol? x)
    [:ko {:msg "Assume variable name is reserved." :name x}]
    :else
    (let [[status ty'] (stx/parse-term def-env ty)]
      (if (= status :ko)
        [:ko {:msg "Cannot parse type in assume step" :type-arg ty :error ty'}]
        (if-not (ty/proper-type? def-env ctx ty')
          [:ko {:msg "Not a proper type in assume step" :type-arg ty :parsed-term ty'}]
          [:ok [def-env
                (u/vcons [x ty'] ctx)
                (u/vcons [x #{}] deps)]])))))  ; XXX: it would be more efficient to use stacks... (lists ?)

(example
 (do-assume-step
  '{test :nothing}
  '[[A ✳]]
  '[[A #{}]]
  'x 'A)
 => '[:ok [{test :nothing}
           [[x A] [A ✳]]
           [[x #{}] [A #{}]]]])

(example
 (do-assume-step
  '{test :nothing}
  '[[x A] [A ✳]]
  '[]
  'y 'x)
 => '[:ko {:msg "Not a proper type in assume step", :type-arg x, :parsed-term x}])

(defn do-discharge-step [def-env ctx deps x]
  #_(println "[discharge] x=" x "deps=" deps)
  (cond
    (not= (ffirst ctx) x)
    (throw (ex-info "Discharge failure: variable not in head of context (please report)." {:variable x :context ctx}))
    (not= (ffirst deps) x)
    (throw (ex-info "Discharge failure: variable not in head of dependencies (please report)." {:variable x :deps deps}))
    :else
    (let [def-env' (reduce (fn [env def-name]
                             #_(println "[discharge-step] env=" env "def-name=" def-name)
                             (assoc env
                                    def-name
                                    (d/handle-local-term-discharge
                                     (u/safe-get def-env def-name)
                                     (ffirst ctx) (second (first ctx)))))
                           def-env (second (first deps)))]
      [def-env' (rest ctx) (rest deps)])))

(defn parse-have-name [have-name]
  (cond
    (not (symbol? have-name))
    [:ko {:msg "Wrong have step: name argument is not a symbol." :name-arg have-name}]
    (stx/reserved-symbol? have-name)
    [:ko {:msg "Wrong have step: name is reserved." :name have-name}]
    :else
    [:ok have-name]))

(defn parse-have-step [script]
  (case (count script)
    4 (let [[ty meth arg] (rest script)]
        [:ok {:have-name nil,
              :have-type ty, :method meth, :have-arg arg}])
    5 (let [[step ty meth arg] (rest script)
            [status have-name] (parse-have-name step)]
        (if (= status :ko)
          [:ko have-name]
          [:ok {:have-name have-name,
                :have-type ty, :method meth, :have-arg arg}]))
    [:ko {:msg "Wrong have step: 3 or 4 arguments needed" :nb-args (dec (count script))}]))

(defn do-have-step [def-env ctx deps name have-type method have-arg]
  ;;(println "[do-have-step] name=" name "have-arg=" have-arg)
  ;;(println "   ctx=" ctx)
  (let [[status term]
        (case method
          (:by :term)
          (stx/parse-term def-env have-arg)
          (:from :abst :abstr :discharge)
          [:ko  {:msg "Explicit hypothesis discharge is not supported anymore. Use implicit discharge.":have-step name}]
          ;; else
          [:ko {:msg "No such method for proof script." :have-name name :method method}])]
    ;; check synthetized term
    (if (= status :ko)
      [:ko {:msg "Cannot perform have step: incorrect term." :have-name name :from term}]
      (do
        (when-timing
            (println "- check step" name))
        (let [term (timing "  => handling specials"
                           ;; XXX: need to remove the specials ASAP
                           (n/special-normalize def-env ctx term)) 
              term' (timing "  => unfolding local definitions"
                            ;; XXX: full normalization should
                            ;; not be needed ...
                            ;; (n/normalize def-env ctx term) ???
                            (n/delta-normalize-local def-env term))
              [status have-type] (if (and (symbol? have-type)
                                          (= (clojure.core/name have-type) "_"))
                                   [:ok nil]
                                   (stx/parse-term def-env have-type))]
          ;;(println "   have-term = " term')
          (if (= status :ko)
            [:ko {:msg "Cannot perform have step: erroneous type." :have-name name :from have-type}]
            (let [[status have-type]
                  (if (nil? have-type)
                    (let [[status have-type] (timing "  => infer step type"
                                                     (ty/type-of-term def-env ctx term'))]
                      (if (= status :ko)
                        [:ko (assoc (dissoc have-type :msg)
                                    :msg (str "Cannot perform have step: " (:msg have-type)))]
                        [:ok have-type]))
                    (let [[status computed-type] (timing "  => compute step type"
                                                         (type-of-term def-env ctx term'))]
                      ;;(println "  [computed-type] = " computed-type)
                      (if (= status :ko)
                        [:ko {:msg "Cannot synthetize term type."
                              :from computed-type}]
                        (if (timing "  => compare with specified type"
                                    (not (n/beta-eq? def-env ctx have-type computed-type)))
                          [:ko {:msg "Cannot perform have step: synthetized term type and expected type do not match."
                                :have-name name
                                :term term :expected-type have-type :synthetized-type computed-type}]
                          [:ok have-type]))))]
              (cond (= status :ko) [:ko have-type]
                    (nil? name) [:ok [def-env ctx]]
                    :else
                    (let [[status tdef] (d/handle-local-term-definition
                                         name
                                         term'
                                         have-type)]
                      ;;(println "[have-step] term=" term)
                      ;;(println "            def=" (:parsed-term tdef))
                      (if (= status :ko)
                        [:ko {:msg "Cannot perform have step: wrong local definition."
                              :have-name name
                              :from tdef}]
                        (let [deps' (mapv (fn [[x xdeps]]
                                            [x (conj xdeps name)]) deps)]
                          [:ok [(assoc def-env name tdef) ctx deps']])))))))))))

(example
 (do-have-step
  {}
  '[[A ✳] [x A]]
  '[[x #{}]]
  'step 'A :by 'x)
 => '[:ok [{step #latte.kernel.defenv.Definition{:name step,
                                                 :params [],
                                                 :arity 0,
                                                 :parsed-term x,
                                                 :type A}} [[A ✳] [x A]] [[x #{step}]]]])


(defn discharge-all [def-env ctx deps]
  #_(println "[discharge-all] deps=" deps)
  (loop [deps deps, ctx ctx, def-env' def-env]
    (if (seq deps)
      (let [[x xdeps] (first deps)
            [_ ty] (first ctx)]
        (recur (rest deps) (rest ctx)
               (reduce (fn [env def-name]
                         (assoc env def-name (d/handle-local-term-discharge (u/safe-get env def-name) x ty)))
                       def-env' xdeps)))
      def-env')))

(defn do-qed-step [def-env ctx deps term]
  (let [def-env' (discharge-all def-env ctx deps)]
    (let [[status term] (stx/parse-term def-env' term)]
      (if (= status :ko)
        [:ko {:msg "Cannot do QED step: parse error." :error term}]
        [:ok (n/delta-normalize-local def-env' term)]))))

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
      (let [term' (n/normalize def-env ctx term)]
        (clojure.pprint/pprint term)
        (let [[status ty] (ty/type-of-term def-env ctx term')] 
          (if (= status :ko)
            (clojure.pprint/pprint ty)
            (do (print "::")
                (clojure.pprint/pprint ty)))))))
  (println "-----------------------------------------"))

(defn do-shownorm-step [def-env ctx arg]
  (println "[shownorm]" arg)
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

(defn evaluate-script [script def-env ctx deps cont-stack]
  #_(println "[evaluate-script] ctx=" ctx "deps=" deps)
  #_(println "---------------------------------------------")
  #_(clojure.pprint/pprint script)
  #_(println "---------------------------------------------")
  (if (seq script)
    (if (sequential? (first script))
      (recur (first script) def-env ctx deps (conj cont-stack (rest script)))
      (if (string? (first script))
        ;; strings are used for comments inside proof scripts
        (recur (rest script) def-env ctx deps cont-stack)
        (case (first script)
          assume
          (let [[status info] (parse-assume-step script)]
            (if (= status :ko)
              [:ko info]
              (let [{[x ty] :binding body :body} info]
                (let [[status res] (do-assume-step def-env ctx deps x ty)]
                  (if (= status :ko)
                    [:ko res]
                    (recur body (first res) (second res) (nth res 2)
                           (conj cont-stack (list 'discharge x))))))))
          discharge
          (let [[def-env' ctx' deps'] (do-discharge-step def-env ctx deps (second script))]
            (recur '() def-env' ctx' deps' cont-stack))
          have
          (let [[status info] (parse-have-step script)]
            (if (= status :ko)
              [:ko info]
              (let [{have-name :have-name have-type :have-type method :method have-arg :have-arg} info]
                (let [[status res] (do-have-step def-env ctx deps have-name have-type method have-arg)]
                  (if (= status :ko)
                    [:ko res]
                    (recur '() (first res) (second res) (nth res 2) cont-stack))))))
          qed
          (do-qed-step def-env ctx deps (second script))
          showdef
          (do (do-showdef-step def-env (second script))
              (recur '() def-env ctx deps cont-stack))
          showterm
          (do (do-showterm-step def-env ctx (second script))
              (recur '() def-env ctx deps cont-stack))
          shownorm
          (do (do-shownorm-step def-env ctx (second script))
              (recur '() def-env ctx deps cont-stack))
          showctx
          (do (do-showctx-step def-env ctx)
              (recur '() def-env ctx deps cont-stack))
          ;; else
          (throw (ex-info "Don't know how to evaluate script." {:script script})))))
    ;; at end of script
    (if (seq cont-stack)
      (recur (first cont-stack) def-env ctx deps (rest cont-stack))
      [:ko {:msg "Incomplete proof (`qed` step missing)."}])))
