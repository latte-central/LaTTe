
(ns latte.kernel.presyntax
  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.defenv :as defenv]
            [latte.kernel.syntax :as stx]))

(def ^:private +examples-enabled+)

(def +reserved-symbols+
  '#{□ ✳ λ Π ⟶ ∃ ∀})

(defn reserved-symbol? [s]
  (or (contains? +reserved-symbols+ s)
      (let [sym (name s)]
        (and (>= (count sym) 2)
             (= (first sym) \_)
             (<= \0 (second sym) \9)))))

(defn kind? [t]
  (contains? '#{:kind □} t))

(defn type? [t]
  (contains? '#{:type ✳} t))

(declare parse-compound-term
         parse-symbol-term)

(defn parse-term
  "Parse a presyntax term `t` in environment `def-env` (for checking references)
at the given `level` (number of binders above) with binders `bmap` (mapping a binder name to a level `k`)."
  ([def-env t] (parse-term def-env t 0 {}))
  ([def-env t level bmap]
   (cond
     (kind? t) [:ok '□]
     (type? t) [:ok '✳]
     (sequential? t) (parse-compound-term def-env t level bmap)
     (symbol? t) (parse-symbol-term def-env t level bmap)
     :else [:ko {:msg "Cannot parse term" :term t}])))

(example
 (parse-term {} :kind) => '[:ok □])

(example
 (parse-term {} :type) => '[:ok ✳])

(defn parse-symbol-term [def-env sym level bmap]
  ;;(println "[parse-symbol-term] sym=" sym)
  (if (reserved-symbol? sym)
    [:ko {:msg "Symbol is reserved" :term sym}]
    (if-let [sym-level (get bmap sym)]
      [:ok (stx/mk-bvar (- level (inc sym-level)))]
      (if (defenv/registered-definition? def-env sym)
        [:ok (stx/mk-ref (defenv/qualify-def def-env sym) [])]
        ;; else it's a free variable
        [:ok (stx/mk-fvar sym)]))))

(example
 (parse-term {} 'x 3 {'x 1}) => [:ok (stx/mk-bvar 1)])

(example
 (parse-term {} 'y 3 {'x 1}) => [:ok (stx/mk-fvar 'y)])

(example
 (parse-term {'x {:arity 0}} 'x)
 => [:ok (stx/mk-ref 'x [])])

(defn lambda-kw? [t]
  (= t 'λ))

(defn product-kw? [t]
  (or (= t 'Π)
      (= t '∀)))

(defn arrow-kw? [t]
  (= t '⟶))

(declare parse-lambda-term
         parse-product-term
         parse-arrow-term
         parse-defined-term
         parse-application-term)

(defn parse-compound-term [def-env t level bmap]
  ;; (println "[parse-compound-term] t=" t)
  (if (empty? t)
    [:ko {:msg "Compound term is empty" :term t}]
    (cond
      (lambda-kw? (first t)) (parse-lambda-term def-env t level bmap)
      (product-kw? (first t)) (parse-product-term def-env t level bmap)
      (arrow-kw? (first t)) (parse-arrow-term def-env t level bmap)
      :else
      (if (and (or (symbol? (first t)) (var? (first t)))
               (defenv/registered-definition? def-env (first t)))
        (let [[status sdef] (defenv/fetch-definition def-env (first t))]
          (cond
            (= status :ko)
            [:ko sdef]
            (not (defenv/latte-definition? sdef))
            (throw (ex-info "Not a LaTTe definition (please report)"
                            {:def sdef}))
            (and (= (:arity sdef) 0)
                 (seq (rest t)))
            (parse-application-term def-env (cons (list (first t)) (rest t)) level bmap)
            :else
            (parse-defined-term def-env sdef t level bmap)))
        ;; else
        (parse-application-term def-env t level bmap)))))

(defn parse-binding [def-env v level bmap]
  (cond
    (not (vector? v))
    [:ko {:msg "Binding is not a vector" :term v}]
    (< (count v) 2)
    [:ko {:msg "Binding must have at least 2 elements" :term v}]
    :else
    (let [ty (last v)
          [status ty'] (parse-term def-env ty level bmap)]
      (if (= status :ko)
        [:ko {:msg "Wrong binding type" :term v :from ty'}]
        (loop [s (butlast v), vars #{}, res []]
          (if (seq s)
            (cond
              (not (symbol? (first s)))
              [:ko {:msg "Binding variable is not a symbol" :term v :var (first s)}]
              (reserved-symbol? (first s))
              [:ko {:msg "Wrong binding variable: symbol is reserved" :term v :symbol (first s)}]
              (contains? vars (first s))
              [:ko {:msg "Duplicate binding variable" :term v :var (first s)}]
              :else (recur (rest s) (conj vars (first s)) (conj res [(first s) ty'])))
            [:ok res]))))))

(example
 (parse-binding {} '[x :type] 0 {})
 => '[:ok [[x ✳]]])

(example
 (parse-binding {} '[x y z :type] 0 {})
 => '[:ok [[x ✳] [y ✳] [z ✳]]])

(example
 (parse-binding {} '[x y Π :type] 0 {})
 => '[:ko {:msg "Wrong binding variable: symbol is reserved",
           :term [x y Π :type],
           :symbol Π}])

(example
 (parse-binding {} '[x y x :type] 0 {})
 => '[:ko {:msg "Duplicate binding variable", :term [x y x :type], :var x}])

(example
 (parse-binding {} '[x] 0 {})
 => '[:ko {:msg "Binding must have at least 2 elements", :term [x]}])

(example
 (parse-binding {} '[x y :bad] 0 {})
 => '[:ko {:msg "Wrong binding type", :term [x y :bad], :from {:msg "Cannot parse term", :term :bad}}])

(defn parse-binder-term [def-env binder t level bmap]
  (if (< (count t) 3)
    [:ko {:msg (str "Wrong " binder " form (expecting at least 3 arguments)") :term t :nb-args (count t)}]
    (let [[status bindings] (parse-binding def-env (second t) level bmap)]
      (if (= status :ko)
        [:ko {:msg (str "Wrong bindings in " binder " form") :term t :from bindings}]
        (let [[bmap' level'] (loop [bindings bindings, level level, bmap bmap]
                               (if (seq bindings)
                                 (recur (rest bindings) (inc level) (assoc bmap (ffirst bindings) level))
                                 [bmap level]))]
          (let [body (if (= (count t) 3)
                       (nth t 2)
                       (rest (rest t)))]
            (let [[status body] (parse-term def-env body level' bmap')]
              (if (= status :ko)
                [:ko {:msg (str "Wrong body in " binder " form") :term t :from body}]
                (let [binder-fun (cond
                                   (lambda-kw? binder) stx/mk-lambda
                                   (product-kw? binder) stx/mk-prod
                                   :else (throw (ex-info "Not a known binder (please report)" {:term t, :binder binder})))]
                  (loop [i (dec (count bindings)), res body]
                    (if (>= i 0)
                      (let [[x ty] (bindings i)]
                        (recur (dec i) (binder-fun x ty res)))
                      [:ok res])))))))))))

(defn parse-lambda-term [def-env t level bmap]
  (parse-binder-term def-env 'λ t level bmap))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x :type] x) 0 {})))
 => '(λ [✳] :0))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x :type] (λ [y :type] y)))))
 => '(λ [✳] (λ [✳] :0)))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x :type] (λ [y :type] x)))))
 => '(λ [✳] (λ [✳] :1)))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x :type] (λ [y :type] z)))))
 => '(λ [✳] (λ [✳] z)))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x y :type] x))))
 => '(λ [✳] (λ [✳] :1)))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x y :type] y))))
 => '(λ [✳] (λ [✳] :0)))

(example
 (parse-term {} '(λ [x x :type] x))
 => '[:ko {:msg "Wrong bindings in λ form",
           :term (λ [x x :type] x),
           :from {:msg "Duplicate binding variable", :term [x x :type], :var x}}])

(example
 (parse-term {} '(λ [x] x))
 => '[:ko {:msg "Wrong bindings in λ form",
           :term (λ [x] x),
           :from {:msg "Binding must have at least 2 elements", :term [x]}}])

(defn parse-product-term [def-env t level bmap]
  (parse-binder-term def-env 'Π t level bmap))

(example
 (stx/unparse-ln (second (parse-term {} '(Π [x :type] x))))
 => '(Π [✳] :0))

(example
 (stx/unparse-ln (second (parse-term {} '(Π [x y :type] x))))
 => '(Π [✳] (Π [✳] :1)))

(defn parse-terms [def-env ts level bmap]
  (reduce (fn [res t]
            (let [[status t' :as tres] (parse-term def-env t level bmap)]
              (if (= status :ok)
                [:ok (conj (second res) t')]
                (reduced tres)))) [:ok []] ts))

(example
 (parse-terms {} '(x y z) 0 {})
 => [:ok [(stx/mk-fvar 'x) (stx/mk-fvar 'y) (stx/mk-fvar 'z)]])

(example
 (parse-terms {} '(x y z) 4 '{x 1, z 2})
 => [:ok [(stx/mk-bvar 2) (stx/mk-fvar 'y) (stx/mk-bvar 1)]])

(defn parse-arrow-term [def-env t level bmap]
  (if (< (count t) 3)
    [:ko {:msg "Arrow (implies) requires at least 2 arguments"
          :term t
          :nb-args (count (rest t))}]
    (let [prod
          (loop [ts (butlast (rest t)), res (last t)]
            (if (seq ts)
              (recur (rest ts) (list 'Π ['⇧ (first ts)] res))
              res))]
      (let [[status res] (parse-term def-env prod level bmap)]
        (if (= status :ko)
          [:ko {:msg "Cannot parse arrow term"
                :term t
                :from res}]
          [:ok res])))))

(example
 (stx/unparse-ln (second (parse-term {} '(⟶ :type :type))))
 => '(Π [✳] ✳))

(example
 (stx/unparse-ln (second (parse-term {} '(⟶ sigma tau mu))))
 => '(Π [tau] (Π [sigma] mu)))

(defn parse-defined-term [def-env sdef t level bmap]
  (if (defenv/notation? sdef)
    (let [notation-fn (defenv/get-notation-fn sdef)
          [status t'] (apply notation-fn (rest t))]
      (if (= status :ko)
        [:ko t']
        (parse-term def-env t' level bmap)))
    ;; other definitions
    (let [def-name (first t)
          arity (count (rest t))]
      (if (and (get sdef :arity)
               (< (:arity sdef) arity))
        [:ko {:msg "Too many arguments for definition." :term t :def-name def-name :arity arity :nb-args (:arity sdef)}]
        ;; else
        (let [[status ts] (parse-terms def-env (rest t) level bmap)]
          (if (= status :ko)
            [:ko {:msg "Wrong argument" :term t :from ts}]
            [:ok (stx/mk-ref (defenv/qualify-def def-env def-name) ts)]))))))

(example
 (stx/unparse-ln (second (parse-term {'ex (defenv/map->Definition {:arity 3})}
                                     '(ex x y :kind) 2 {'x 1})))
 => '(ex :0 y □))

(example
 (stx/unparse-ln (second (parse-term {'ex (defenv/map->Definition {:arity 3})}
                                 '(ex x y z) 3 '{x 0 y 1 z 2})))
 => '(ex :2 :1 :0))

(defn parse-application-term [def-env t level bmap]
  ;; (println "[parse-application-term] t=" t)
  (if (< (count t) 2)
    [:ko {:msg "Application needs at least 2 terms" :term t :nb-terms (count t)}]
    (let [[status ts] (parse-terms def-env t level bmap)]
      ;; (println "   ==> " (left-binarize ts))
      (if (= status :ko)
        [:ko {:msg "Parse error in operand of application" :term t :from ts}]
        [:ok (apply stx/mk-app ts)]))))

(example
 (stx/unparse-ln (second (parse-term {} '(x y) 3 '{x 1, y 2})))
 => '(:1 :0))

(example
 (stx/unparse-ln (second (parse-term {} '(x y z) 3 '{x 1, y 2})))
 => '(:1 :0 z))

(example
 (stx/unparse-ln (second (parse-term {} '(t x y z) 3 '{x 1, y 2})))
 => '(t :1 :0 z))

(example
 (stx/unparse-ln (second (parse-term {} '(λ [x :type] x :type :kind))))
 => '(λ [✳] (:0 ✳ □)))

(defn parse
  ([t] (parse {} t))
  ([def-env t] (let [[status t'] (parse-term def-env t)]
                 (if (= status :ko)
                   (throw (ex-info "Parse error" t'))
                   t'))))

