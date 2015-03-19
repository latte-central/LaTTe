
(ns latte.termparser)

(def ^:dynamic *term-list-parsers* (atom {}))
(def ^:dynamic *term-other-parsers* (atom []))

(defn fetch-term-list-parsers
  "Fetch the current parsers for list-based terms."
  []
  (deref *term-list-parsers*))

(defn fetch-term-other-parsers
  "Fetch the current other (non-list) term parsers."
  []
  (deref *term-other-parsers*))

(defn register-term-list-parser
  "Register the parser function `pfun` for
  list-based term type `typ`."
  [typ pfun]
  (swap! *term-list-parsers* (fn [parsers] (assoc parsers typ pfun))))

(defn register-term-other-parser
  "Register the parser function `pfun` for
  (non-list) terms recognized by `pmatch?`."
  [pmatch? pfun]
  (swap! *term-other-parsers* (fn [parsers] (conj parsers [pmatch?, pfun]))))

(defn- parse-list-term [expr bind-env]
  (if (empty? expr)
    (throw (Exception. "Parse error: empty-list"))
    (let [parser (get (fetch-term-list-parsers) (first expr) :not-found)]
      (if (= parser :not-found)
        (throw (Exception. (str "Parse error: don't know how to parse '" (first expr) "'-expressions")))
        (parser expr bind-env)))))

(defn- parse-other-term [expr parsers bind-env]
  (if (seq parsers)
    (let [[match?, parser] (first parsers)]
      (if (match? expr bind-env)
        (parser expr bind-env)
        (recur expr (rest parsers) bind-env)))
    (throw (Exception. (str "Parse error: don't know how to parse '" expr "'")))))

(defn parse-list-check-arity
  "Check `arity` of `expr` list-term."
  [expr arity]
  (if (not= (count expr) (+ arity 1))
    (throw (Exception. (str "Wrong arity: expect " arity " argument" (if (> arity 1) "s" "") " for '" (first expr) "'-expressions, given: " (- (count expr) 1))))
    true))

(defn parse
  "Parse a term from the expression `expr`,
  or signal a parsing problem."
  ([expr] (parse expr []))
  ([expr bind-env]
   (let [[parsed?, result]
     (if (list? expr)
       (if (empty? expr)
         (throw (Exception. "Parse error: empty-list"))
         (if-let [parser (get (fetch-term-list-parsers) (first expr))]
           [true, (parser expr bind-env)]
           [false, nil]))
       ;; not a list
       [false, nil])]
     (if parsed?
       result
       (parse-other-term expr (deref *term-other-parsers*) bind-env)))))

