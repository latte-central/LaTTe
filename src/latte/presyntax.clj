
(ns latte.presyntax
  (:require [clj-by.example :refer [example do-for-example]])
  )

(def ^:private +examples-enabled+)

(def +reserved-symbols+
  '#{kind type □ * ∗ ✳ lambda λ prod forall ∀ _arrow})

(defn reserved-symbol? [s]
  (or (contains? +reserved-symbols+ s)
      (= (first (name s)) \_)))

(defn kind? [t]
  (contains? '#{:kind □} t))

(defn type? [t]
  (contains? '#{:type * ∗ ✳} t))

(declare parse-compound-term
         parse-symbol-term)

(defn parse-term
  ([def-env t] (parse-term def-env t #{}))
  ([def-env t bound]
   (cond
     (kind? t) [:ok :kind]
     (type? t) [:ok :type]
     (list? t) (parse-compound-term def-env t bound)
     (symbol? t) (parse-symbol-term def-env t bound)
     :else [:ko {:msg "Cannot parse term" :term t}])))

(example
 (parse-term {} :kind) => [:ok :kind])

(example
 (parse-term {} '*) => [:ok :type])

(defn parse-symbol-term [def-env sym bound]
  (cond
    (reserved-symbol? sym) [:ko {:msg "Symbol is reserved" :term sym}]
    (contains? bound sym) [:ok sym]
    (contains? def-env sym)
    (let [sdef (get def-env sym)]
      (if (not= (:arity sdef) 0)
        [:ko {:msg "Definition is not a constant (arity>0)" :term sym :def sdef}]
        [:ok (list sym)]))
    ;; free variable
    :else [:ok sym]))

(example
 (parse-term {} 'x #{'x}) => '[:ok x])

(example
 (parse-term {} 'x #{'y}) => '[:ok x])

(example
 (parse-term {'x {:arity 0}} 'x)
 => '[:ok (x)])

(example
 (parse-term {'x {:arity 1}} 'x)
 => '[:ko {:msg "Definition is not a constant (arity>0)",
           :term x, :def {:arity 1}}])

(defn lambda-kw? [t]
  (contains? #{'lambda 'λ} t))

(defn product-kw? [t]
  (contains? #{'prod 'pi 'Π 'forall '∀} t))

(defn arrow-kw? [t]
  (contains? #{'imply '--> '-> '=> '==> '→ '➝ '⟶ '⟹} t))

(declare parse-lambda-term
         parse-product-term
         parse-arrow-term
         parse-defined-term
         parse-application-term)

(defn parse-compound-term [def-env t bound]
  (if (empty? t)
    [:ko {:msg "Compound term is empty" :term t}]
    (cond
      (lambda-kw? (first t)) (parse-lambda-term def-env t bound)
      (product-kw? (first t)) (parse-product-term def-env t bound)
      (arrow-kw? (first t)) (parse-arrow-term def-env t bound)
      (contains? def-env (first t)) (parse-defined-term def-env t bound)
      :else (parse-application-term def-env t bound))))

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
 => '[:ok [[x :type]]])

(example
 (parse-binding {} '[x y z :type] #{})
 => '[:ok [[x :type] [y :type] [z :type]]])

(example
 (parse-binding {} '[x y forall :type] #{})
 => '[:ko {:msg "Wrong binding variable: symbol is reserved",
           :term [x y forall :type],
           :symbol forall}])

(example
 (parse-binding {} '[x y x :type] #{})
 => '[:ko {:msg "Duplicate binding variable", :term [x y x :type], :var x}])

(example
 (parse-binding {} '[x] #{})
 => '[:ko {:msg "Binding must have at least 2 elements", :term [x]}])

(example
 (parse-binding {} '[x y :bad] #{})
 => '[:ko {:msg "Wrong binding type", :term [x y :bad], :from {:msg "Cannot parse term", :term :bad}}])

(defn vconcat [v1 v2]
  (loop [s v2, v v1]
    (if (seq s)
      (recur (rest s) (conj v (first s)))
      v)))

(example
 (concat [1 2 3] [4 5 6]) => [1 2 3 4 5 6])

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
  (parse-binder-term def-env 'lambda t bound))

(example
 (parse-term {} '(lambda [x :type] x))
 => '[:ok (lambda [x :type] x)])

(example
 (parse-term {} '(lambda [x y :type] x))
 => '[:ok (lambda [x :type] (lambda [y :type] x))])

(example
 (parse-term {} '(lambda [x x :type] x))
 => '[:ko {:msg "Wrong bindings in lambda form",
           :term (lambda [x x :type] x),
           :from {:msg "Duplicate binding variable", :term [x x :type], :var x}}])

(example
 (parse-term {} '(lambda [x] x))
 => '[:ko {:msg "Wrong bindings in lambda form",
           :term (lambda [x] x),
           :from {:msg "Binding must have at least 2 elements", :term [x]}}])

(example
 (parse-term {} '(lambda [x :type] z))
 => '[:ok (lambda [x :type] z)])

(defn parse-product-term [def-env t bound]
  (parse-binder-term def-env 'prod t bound))

(example
 (parse-term {} '(forall [x :type] x))
 => '[:ok (prod [x :type] x)])

(example
 (parse-term {} '(prod [x y :type] x))
 => '[:ok (prod [x :type] (prod [y :type] x))])

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
            (recur (rest ts) (list 'prod ['_arrow (first ts)] res))
            [:ok res]))))))

(example
 (parse-term {} '(--> :type :type))
 => '[:ok (prod [_arrow :type] :type)])

(example
 (parse-term {} '(--> sigma tau mu))
 => '[:ok (prod [_arrow sigma] (prod [_arrow tau] mu))])

(defn parse-defined-term [def-env t bound]
  (let [def-name (first t)
        sdef (get def-env (first t))
        arity (count (rest t))]
    (if (not= (:arity sdef) arity)
      [:ko {:msg "Wrong arity for defined term." :term t :arity arity :def-arity (:arity sdef)}]
      (let [[status ts] (parse-terms def-env (rest t) bound)]
        (if (= status :ko)
          [:ko {:msg "Wrong argument" :term t :from ts}]
          [:ok (list* def-name ts)])))))

(example
 (parse-term {'ex {:arity 2}}
             '(ex x :kind) #{'x})
 => '[:ok (ex x :kind)])

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
  (if (< (count t) 2)
    [:ko {:msg "Application needs at least 2 terms" :term t :nb-terms (count t)}]
    (let [[status ts] (parse-terms def-env t bound)]
      (if (= status :ko)
        [:ko {:msg "Parse error in operand of application" :term t :from ts}]
        [:ok (left-binarize ts)]))))

(example
 (parse-term {} '(x y) '#{x y}) => '[:ok [x y]])

(example
 (parse-term {} '(x y z) '#{x y z}) => '[:ok [[x y] z]])

(example
 (parse-term {} '(lambda [x :type] x :type :kind))
 => '[:ok (lambda [x :type] [[x :type] :kind])])


(defn parse
  ([t] (parse {} t))
  ([def-env t] (let [[status t'] (parse-term def-env t)]
                 (if (= status :ko)
                   (throw (ex-info "Parse error" t'))
                   t'))))


