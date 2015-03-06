
;;{

;; # Miscellaneous utilities

;; The `latte.utils` namespace provides a few
;; programming utilies for the rest of the project.

;;}

(ns latte.utils)

;;{

;; ## Inline examples

;; The `example` macro is the Lisp utility I use to
;; support my litterate-programming style, providing
;; inline examples that may also be run as tests, if
;; the `*examples-enabled*` dynamic variable is rebound
;; to a truthy value (most likely `true`).

;;}

(def ^:dynamic *examples-enabled*)

(comment
  (example (+ 2 (* 3 5)) => (+ 4 13))

  ;; should yield:

  (let [res (+ 2 (* 3 5))
        val (+ 4 13)]
    (if (= res val)
      val
      (throw ex-info "Example failed" {:expr '(+ 2 (* 3 5))
                                       :val '17 })))
  )

(comment

  ;;  a few macro reminders
  
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

)

(defmacro example
  "Show as an example the evaluation of `expr` as `val`.
  Throws an exception is `*examples-enabled*`"
  [expr sep val & {:keys [equiv?]
                   :or { equiv? = }}]
  (when (not= (name sep) "=>")
    (throw (ex-info "Missing '=>' in example" {:expr `(quote ~expr)
                                               :sep `(quote ~sep)
                                               :val `(quote ~val)})))
  (when *examples-enabled*
    `(let [expr# ~expr
           val# ~val]
       (if (~equiv? expr# val#)
         val#
         (throw (ex-info "Example failed" {:expr ~`(quote ~expr)
                                           :val  ~`(quote ~val) }))))))

;;  (macroexpand-1 '(example (+ 2 12) => 13))
