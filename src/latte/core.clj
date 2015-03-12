(ns latte.core
  (:require [latte.utils :as utils :refer [example]]
            [latte.term :as term :refer [unparse mk-univ]]
            [latte.termparser :as parser])
  (:gen-class))

(def ^:dynamic *examples-enabled* true)

(def tset (mk-univ 0))

;(defmethod print-method latte.term.Univ [v ^java.io.Writer w]
;  (.write w (str (unparse v))))



;; (defn impl-refl
;;   "Reflexivity of implication, at level `l` (defaults to `0`)."
;;   ([u] (term (lambda [a ~u] a)))
;;   ([] (impl-refl 0)))

;; (defterm impl-refl [u 0]
;;   (lambda [a ~u] a))

;; (defn and-commute
;;   "Commutativity of cojunction."
;;   ([u v] (term (lambda [a ~u, b ~v]
;;                        (lambda [h (forall [x a, y b] (and x y))]
;;                                [(second h
  
(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!")
  (println (str "Universe of level 2 = " (unparse (mk-univ 2))))
  (println (str "The set of basic types = " tset))
  (println (example 12 => 12))
  )
