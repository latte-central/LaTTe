
(ns latte.utils)

(def ^:dynamic *examples-enabled* true)


;; (example (+ 2 (* 3 5)) => (+ 4 13))

(let [res (+ 2 (* 3 5))
      val (+ 4 13)]
  (if (= res val)
    val
    (throw ex-info "Example failed" {:expr '(+ 2 (* 3 5))
                                     :val '17 })))

;(let [res (+ 2 (* 3 5))
;      val (+ 4 12)]
;  (if (= res val)
;    val
;    (throw (ex-info "Example failed" {:expr '(+ 2 (* 3 5))
;                                      :val '17 }))))

(defmacro myquote
  [expr]
  `(quote ~expr))

(myquote (+ 2 3))

(macroexpand '(myquote (+ 2 3)))

(defmacro double-eval-once
  [expr]
  `(let [expr# ~expr]
     (+ expr# expr#)))

(double-eval-once (+ 3 4))

(macroexpand '(double-eval-once (+ 3 4)))

(defmacro example
  "Show as an example the evaluation of `expr` as `val`.
  Throws an exception is `*examples-enabled*`"
  [expr sep val & {:keys [equiv?]
                   :or { equiv? = }}]
  (when (not= (name sep) "=>")
    (throw (ex-info "Missing '=>' in example" {:expr `(quote ~expr)
                                               :sep `(quote ~sep)
                                               :val `(quote ~val)})))
  (if *examples-enabled*
    `(let [expr# ~expr
           val# ~val]
       (if (~equiv? expr# val#)
         val#
         (throw (ex-info "Example failed" {:expr ~`(quote ~expr)
                                           :val  ~`(quote ~val) }))))
    nil))
         
(def ^:dynamic *examples-enabled* true)

(macroexpand '(example (+ 2 12) => 13))
