(ns latte.core
  (:require [latte.utils :as utils :refer [example]]
            [latte.term :as term :refer [mk-univ]])
  (:gen-class))

(def ^:dynamic *examples-enabled* true)

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!")
  (println (str "Universe of level 2 = " (mk-univ 2)))
  (println (example 12 => 12))
  )
