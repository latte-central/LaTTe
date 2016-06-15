
(ns typetheory.syntax
  (:require [clj-by.example :refer [example do-for-example]])
  (:require [clojure.spec :as s])
  (:require [clojure.test.check :as tc])
  (:require [clojure.test.check.generators :as gen])
  (:require [clojure.test.check.properties :as prop])
  )

;;{
;; # The syntax of type theory
;;}

(def ^:private +examples-enabled+)

;;{
;; ## Lambda terms
;;}

(s/def ::kind #{:kind})

(example
 (s/valid? ::kind :kind) => true)

(s/def ::type #{:type})

(example
 (s/valid? ::type :type) => true)

(s/def ::sort (s/or :kind ::kind
                    :type ::type))

(example
 (s/valid? ::sort :kind) => true)

(example
 (s/valid? ::sort :type) => true)

(s/def ::var symbol?)

(example
 (s/valid? ::var 'x) => true)

(s/def ::binder #{'lambda 'prod})

(s/def ::binding (s/tuple ::var ::term))

(s/def ::bind (s/cat :binder ::binder :binding ::binding :body ::term))

(s/def ::product (s/cat :prod #{'prod} :binding ::binding :body ::term))

(s/def ::app (s/cat :rator ::term :rand ::term))

(s/def ::ref #{:ref})

(s/def ::refered (s/cat :name symbol? :args (s/* ::term)))

(s/def ::refer (s/tuple ::ref ::refered))

(s/def ::term
  (s/or :kind ::kind
        :type ::type
        :var ::var
        :bind ::bind
        :app ::app
        :refer ::refer))

(example
 (s/conform ::term :kind) => [:kind :kind])

(example
 (s/conform ::term :type) => [:type :type])

(example
 (s/conform ::term 'x) => [:var 'x])

(example
 (s/conform ::term '(x y))
 => '[:app {:rator [:var x], :rand [:var y]}])

(example
 (s/conform ::term '(lambda [x :kind] (x y)))
 => '[:bind {:binder lambda,
             :binding [x [:kind :kind]],
             :body [:app {:rator [:var x],
                          :rand [:var y]}]}])

(example
 (s/conform ::term '(prod [x :kind] (x y)))
 => '[:bind {:binder prod,
             :binding [x [:kind :kind]],
             :body [:app {:rator [:var x],
                          :rand [:var y]}]}])

(example
 (s/valid? ::product '(prod [x :kind] (x y))) => true)

(example
 (s/conform ::term '[:ref (test x [:ref (test2 y z)] t)])
 => '[:refer [:ref {:name test,
                    :args [[:var x] [:refer [:ref {:name test2,
                                                   :args [[:var y] [:var z]]}]] [:var t]]}]])

(defmacro conform [s v]
  `(let [v# (s/conform ~s ~v)]
     (if (= v# :clojure.spec/invalid)
       nil
       v#)))

(example
 (conform ::term '(x y)) => (s/conform ::term '(x y)))

(example
 (conform ::term :toto) => nil)

(defmacro validate [s v]
  `(if-let [res# (conform ~s ~v)]
     res#
     (throw (ex-info (str "Invalid " (quote ~s)) {:value (quote ~v) :explain (s/explain-data ~s ~v)}))))

;;{
;; ## Free and bound variables
;;}

(defn free-vars- [[tag t]]
  (case tag
    :var #{t}
    :bind (clojure.set/difference (free-vars- (:body t))
                                  #{(first (:binding t))})
    :app (clojure.set/union (free-vars- (:rator t))
                            (free-vars- (:rand t)))
    :refer (apply clojure.set/union (map free-vars- (:args (second t))))
    #{}))

(defn free-vars [t]
  (free-vars- (validate ::term t)))

(example
 (free-vars 'x) => #{'x}) 

(example
 (free-vars '(x y)) => #{'x 'y})

(example
 (free-vars '(lambda [x t] (x (y z)))) => #{'y 'z})

(example
 (free-vars '(prod [x t] (x (y z)))) => #{'y 'z})

(example
 (free-vars '(lambda [x t] [:ref (test x y z)])) => '#{y z})

(defn vars- [[tag t]]
  (case tag
    :var #{t}
    :bind (recur (:body t))
    :app (clojure.set/union (vars- (:rator t))
                            (vars- (:rand t)))
    :refer (apply clojure.set/union (map vars- (:args (second t))))
    #{}))

(defn vars [t]
  (vars- (validate ::term t)))

(example
 (vars 'x) => #{'x}) 

(example
 (vars '(x y)) => #{'x 'y})

(example
 (vars '(lambda [x t] (x (y z)))) => #{'x 'y 'z})

(example
 (vars '(prod [x t] (x (y z)))) => #{'x 'y 'z})

(example
 (vars '(lambda [x t] [:ref (test x y z)])) => '#{x y z})

(defn bound-vars [t]
  (let [t (validate ::term t)]
    (clojure.set/difference (vars- t) (free-vars- t))))

(example
 (bound-vars 'x) => #{}) 

(example
 (bound-vars '(x y)) => #{})

(example
 (bound-vars '(lambda [x t] (x (y z)))) => #{'x})

(example
 (bound-vars '(prod [x t] (x (y z)))) => #{'x})

(example
 (bound-vars '(lambda [x t] [:ref (test x y z)])) => '#{x})

(def vars-free-union-bound
  (prop/for-all
   [t (s/gen ::term)]
   (= (clojure.set/union (free-vars t) (bound-vars t))
      (vars t))))

(example
 (:result (tc/quick-check 20 vars-free-union-bound)) => true)

;;{
;; ## Substitution
;;}

(defn mk-fresh [base forbid]
  (if (contains? forbid base)
    (recur (symbol (str (name base) "'")) forbid)
    base))

(example
 (mk-fresh 'x '#{x x' x''}) => 'x''')

(s/def ::subst (s/map-of ::var ::term))

(defn subst- [[tag t] sub forbid]
  (case tag
    :var [(get sub t t) forbid]
    :bind (let [{binder :binder [x ty] :binding body :body} t
                [x' sub' forbid']
                (if (contains? forbid x)
                  (let [x' (mk-fresh x forbid)]
                    [x' (assoc sub x x') (conj forbid x')])
                  [x sub forbid])
                [ty' forbid''] (subst- ty sub forbid')
                [body' forbid'''] (subst- body sub' forbid'')]
            [(list binder [x' ty'] body')
             forbid'''])
    :app (let [[rator forbid'] (subst- (:rator t) sub forbid)
               [rand forbid''] (subst- (:rand t) sub forbid')]
           [(list rator rand) forbid''])
    [t forbid]))

(defn subst
  ([t sub] (let [t (validate ::term t)]
             (first (subst- t sub (free-vars- t)))))
  ([t k v & kvs] (subst t (apply hash-map (cons k (cons v kvs)))))) 

(example
 (subst 'x {'x :type}) => :type)

(example
 (subst 'y {'x :type}) => 'y)

(example
 (subst '(y x) {'x :type}) => '(y :type))

(example
 (subst '(x (lambda [x :type] (y x))) {'x :type})
 => '(:type (lambda [x' :type] (y x'))))

(example
 (subst '(x (prod [x :type] (y x))) {'x :type, 'y 'x})
 => '(:type (prod [x' :type] (x x'))))
;; and not: '(:type (prod [x :type] (x x)))


;;{
;; ## Alpha-equivalence
;;}

(defn alpha-norm- [[tag t] sub level]
  (case tag
    :var [(get sub t t) level]
    :bind (let [{binder :binder [x ty] :binding body :body} t
                x' (symbol (str "_" level))
                [ty' level'] (alpha-norm- ty sub (inc level))
                [body' level''] (alpha-norm- body (assoc sub x x') level')]
            [(list binder [x' ty'] body')
             level''])
    :app (let [[left' level'] (alpha-norm- (:left t) sub level)
               [right' level''] (alpha-norm- (:right t) sub level')]
           [(list left' right')
            level''])
    [t level]))

(defn alpha-norm [t]
  (let [[t' _] (alpha-norm- (validate ::term t) {} 1)]
    t'))

(example
 (alpha-norm 'x) => 'x)

(example
 (alpha-norm '(lambda [x :type] x))
 => '(lambda [_1 :type] _1))

(defn alpha-eq? [t1 t2]
  (= (alpha-norm t1)
     (alpha-norm t2)))

(example
 (alpha-eq? '(lambda [x :type] x)
            '(lambda [y :type] y)) => true)


(def alpha-eq-refl
  (prop/for-all
   [t (s/gen ::term)]
   (alpha-eq? t t)))

(example
 (:result (tc/quick-check 20 alpha-eq-refl)) => true)

;; Remark: symmetry and transitivity are harder to test...
