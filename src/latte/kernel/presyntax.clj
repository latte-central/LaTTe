
(ns latte.kernel.presyntax
  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.defenv :as defenv]))

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
  ([def-env t] (parse-term def-env t #{}))
  ([def-env t bound]
   (cond
     (kind? t) [:ok '□]
     (type? t) [:ok '✳]
     (sequential? t) (parse-compound-term def-env t bound)
     (symbol? t) (parse-symbol-term def-env t bound)
     :else [:ko {:msg "Cannot parse term" :term t}])))

(example
 (parse-term {} :kind) => '[:ok □])

(example
 (parse-term {} :type) => '[:ok ✳])

(defn parse-symbol-term [def-env sym bound]
  ;;(println "[parse-symbol-term] sym=" sym)
  (cond
    (reserved-symbol? sym) [:ko {:msg "Symbol is reserved" :term sym}]
    (contains? bound sym) [:ok sym]
    (defenv/registered-definition? def-env sym) [:ok (list (defenv/qualify-def def-env sym))]
    :else
    ;; free variable
    [:ok sym]))

(example
 (parse-term {} 'x #{'x}) => '[:ok x])

(example
 (parse-term {} 'x #{'y}) => '[:ok x])

(example
 (parse-term {'x {:arity 0}} 'x)
 => '[:ok (x)])

(example
 (parse-term {'x {:arity 1}} 'x)
 => '[:ok (x)])

(defn lambda-kw? [t]
  (= t 'λ))

(defn product-kw? [t]
  (or (= t 'Π)
      (= t '∀)))

(defn arrow-kw? [t]
  (= t '⟶))

(defn exists-kw? [t]
  (= t '∃))

(declare parse-lambda-term
         parse-product-term
         parse-arrow-term
         parse-exists-term
         parse-defined-term
         parse-application-term)

(defn parse-compound-term [def-env t bound]
  ;; (println "[parse-compound-term] t=" t)
  (if (empty? t)
    [:ko {:msg "Compound term is empty" :term t}]
    (cond
      (lambda-kw? (first t)) (parse-lambda-term def-env t bound)
      (product-kw? (first t)) (parse-product-term def-env t bound)
      (arrow-kw? (first t)) (parse-arrow-term def-env t bound)
      (exists-kw? (first t)) (parse-exists-term def-env t bound)
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
            (parse-application-term def-env (cons (list (first t)) (rest t)) bound)
            :else
            (parse-defined-term def-env sdef t bound)))
        ;; else
        (parse-application-term def-env t bound)))))

(defn parse-binding [def-env v bound]
  (cond
    (not (vector? v))
    [:ko {:msg "Binding is not a vector" :term v}]
    (< (count v) 2)
    [:ko {:msg "Binding must have at least 2 elements" :term v}]
    :else
    (let [ty (last v)
          [status ty'] (parse-term def-env ty bound)]
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
 (parse-binding {} '[x :type] #{})
 => '[:ok [[x ✳]]])

(example
 (parse-binding {} '[x y z :type] #{})
 => '[:ok [[x ✳] [y ✳] [z ✳]]])

(example
 (parse-binding {} '[x y Π :type] #{})
 => '[:ko {:msg "Wrong binding variable: symbol is reserved",
           :term [x y Π :type],
           :symbol Π}])

(example
 (parse-binding {} '[x y x :type] #{})
 => '[:ko {:msg "Duplicate binding variable", :term [x y x :type], :var x}])

(example
 (parse-binding {} '[x] #{})
 => '[:ko {:msg "Binding must have at least 2 elements", :term [x]}])

(example
 (parse-binding {} '[x y :bad] #{})
 => '[:ko {:msg "Wrong binding type", :term [x y :bad], :from {:msg "Cannot parse term", :term :bad}}])

(defn parse-binder-term [def-env binder t bound]
  (if (< (count t) 3)
    [:ko {:msg (str "Wrong " binder " form (expecting at least 3 arguments)") :term t :nb-args (count t)}]
    (let [[status bindings] (parse-binding def-env (second t) bound)]
      (if (= status :ko)
        [:ko {:msg (str "Wrong bindings in " binder " form") :term t :from bindings}]
        (let [bound' (reduce (fn [res [x _]]
                               (conj res x)) #{} bindings)]
          (let [body (if (= (count t) 3)
                       (nth t 2)
                       (rest (rest t)))]
            (let [[status body] (parse-term def-env body bound')]
              (if (= status :ko)
                [:ko {:msg (str "Wrong body in " binder " form") :term t :from body}]
                (loop [i (dec (count bindings)), res body]
                  (if (>= i 0)
                    (recur (dec i) (list binder (bindings i) res))
                    [:ok res]))))))))))

(defn parse-lambda-term [def-env t bound]
  (parse-binder-term def-env 'λ t bound))

(example
 (parse-term {} '(λ [x :type] x))
  => '[:ok (λ [x ✳] x)])

(example
 (parse-term {} '(λ [x y :type] x))
 => '[:ok (λ [x ✳] (λ [y ✳] x))])

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

(example
 (parse-term {} '(λ [x :type] z))
 => '[:ok (λ [x ✳] z)])

(defn parse-product-term [def-env t bound]
  (parse-binder-term def-env 'Π t bound))

(example
 (parse-term {} '(Π [x :type] x))
 => '[:ok (Π [x ✳] x)])

(example
 (parse-term {} '(Π [x y :type] x))
 => '[:ok (Π [x ✳] (Π [y ✳] x))])

(defn parse-terms [def-env ts bound]
  (reduce (fn [res t]
            (let [[status t' :as tres] (parse-term def-env t bound)]
              (if (= status :ok)
                [:ok (conj (second res) t')]
                (reduced tres)))) [:ok []] ts))

(example
 (parse-terms {} '(x y z) #{'x 'y 'z})
 => '[:ok [x y z]])

(example
 (parse-terms {} '(x y z) #{'x 'z})
 => '[:ok [x y z]])

(defn parse-arrow-term [def-env t bound]
  (if (< (count t) 3)
    [:ko {:msg "Arrow (implies) requires at least 2 arguments"
          :term t
          :nb-args (count (rest t))}]
    (let [[status ts'] (parse-terms def-env (rest t) bound)]
      (if (= status :ko)
        [:ko {:msg "Cannot parse arrow." :term t :from ts'}]
        (loop [ts (rest (reverse ts')), res (last ts')]
          (if (seq ts)
            (recur (rest ts) (list 'Π ['⇧ (first ts)] res))
            [:ok res]))))))

(example
 (parse-term {} '(⟶ :type :type))
 => '[:ok (Π [⇧ ✳] ✳)])

(example
 (parse-term {} '(⟶ sigma tau mu))
 => '[:ok (Π [⇧ sigma] (Π [⇧ tau] mu))])

(defn parse-exists-term [def-env t bound]
  (if (< (count t) 3)
    [:ko {:msg (str "Wrong `exists` form (expecting at least 3 arguments)") :term t :nb-args (count t)}]
    (let [[status bindings] (parse-binding def-env (second t) bound)]
      (if (= status :ko)
        [:ko {:msg (str "Wrong bindings in `exists` form") :term t :from bindings}]
        (let [bound' (reduce (fn [res [x _]]
                               (conj res x)) #{} bindings)]
          (let [body (if (= (count t) 3)
                       (nth t 2)
                       (rest (rest t)))]
            (let [[status body] (parse-term def-env body bound')]
              (if (= status :ko)
                [:ko {:msg (str "Wrong body in `exists` form") :term t :from body}]
                (loop [i (dec (count bindings)), res body]
                  (if (>= i 0)
                    (recur (dec i) (list (resolve 'latte.quant/ex) (second (bindings i)) (list 'λ (bindings i) res)))
                    [:ok res]))))))))))

(example
 (parse-term {} '(∃ [x T] P))
 => [:ok (list (resolve 'latte.quant/ex) 'T '(λ [x T] P))])

(defn parse-defined-term [def-env sdef t bound]
  (if (defenv/notation? sdef)
    (let [notation-fn (defenv/get-notation-fn sdef)
          [status t'] (apply notation-fn (rest t))]
      (if (= status :ko)
        [:ko t']
        (parse-term def-env t' bound)))
    ;; other definitions
    (let [def-name (first t)
          arity (count (rest t))]
      (if (and (get sdef :arity)
               (< (:arity sdef) arity))
        [:ko {:msg "Too many arguments for definition." :term t :def-name def-name :arity arity :nb-args (:arity sdef)}]
        ;; else
        (let [[status ts] (parse-terms def-env (rest t) bound)]
          (if (= status :ko)
            [:ko {:msg "Wrong argument" :term t :from ts}]
            [:ok (list* (defenv/qualify-def def-env def-name) ts)]))))))

(example
 (parse-term {'ex (defenv/map->Definition {:arity 2})}
             '(ex x :kind) #{'x})
 => '[:ok (ex x □)])

(example
 (parse-term {'ex (defenv/map->Definition {:arity 3})}
             '(ex x y z) '#{x y z})
 => '[:ok (ex x y z)])

(defn left-binarize [t]
  (if (< (count t) 2)
    t
    (loop [s (rest (rest t)), res [(first t) (second t)]]
      (if (seq s)
        (recur (rest s) [res (first s)])
        res))))

(example
 (left-binarize '(a b)) => '[a b])

(example
 (left-binarize '(a b c)) => '[[a b] c])

(example
 (left-binarize '(a b c d e)) => '[[[[a b] c] d] e])

(defn parse-application-term [def-env t bound]
  ;; (println "[parse-application-term] t=" t)
  (if (< (count t) 2)
    [:ko {:msg "Application needs at least 2 terms" :term t :nb-terms (count t)}]
    (let [[status ts] (parse-terms def-env t bound)]
      ;; (println "   ==> " (left-binarize ts))
      (if (= status :ko)
        [:ko {:msg "Parse error in operand of application" :term t :from ts}]
        [:ok (left-binarize ts)]))))

(example
 (parse-term {} '(x y) '#{x y}) => '[:ok [x y]])

(example
 (parse-term {} '(x y z) '#{x y z}) => '[:ok [[x y] z]])

(example
 (parse-term {} '(x y z t) '#{x y z t}) => '[:ok [[[x y] z] t]])

(example
 (parse-term {} '(λ [x :type] x :type :kind))
 => '[:ok (λ [x ✳] [[x ✳] □])])


(defn parse
  ([t] (parse {} t))
  ([def-env t] (let [[status t'] (parse-term def-env t)]
                 (if (= status :ko)
                   (throw (ex-info "Parse error" t'))
                   t'))))
