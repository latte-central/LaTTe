
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
  (non-list) terms."
  [pfun]
  (swap! *term-other-parsers* (fn [parsers] (conj parsers pfun))))

;; (defn parse-term
;;   "Parse a term from the expression `expr`,
;;   or signal a parsing problem."
;;   [expr]
;;   (if (list? expr)
;;     (if (empty? expr)
;;       (throw (Exception. "Parse error: empty-list"))
;;       (let [parser (get (fetch-term-list-parsers) (car expr) :not-found)]
;;         (if (= parser :not-found)
;;           (throw (Exception. (str "Parse error: don't know how to parse '" (car expr) "'")))
;;           (parser expr))))
;;     (doseq [parser ;; TODO
