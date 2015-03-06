(ns latte.core
  (:require [latte.utils :as utils :refer [example]]
            [latte.term :as term :refer [mk-univ]])
  (:gen-class))

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!")
  (println (str "Universe of level 2 = " (mk-univ 2)))
  )
