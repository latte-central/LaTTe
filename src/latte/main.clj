(ns latte.main
  "The entry point for LaTTe as a standalone tool.
  This is mainly for certifying the core library (target `certify`)
  but other functionalities are provided, like listing axioms, etc."

  (:gen-class)
  
  (:require [latte.utils :as u]
            [latte.prop]
            [latte.equal]
            [latte.quant]
            [latte.classic]
            [latte.fun]
            [latte.certify :as cert]))

(defn run-header []
  (println "*** LaTTe : a proof assistant library for Clojure ***")
  (println "Copyright (C) 2018 Frederic Peschanski (fredokun) under the MIT License.")
  (println "----"))

(defn run-doc
  [library-name]
  (println "Available LaTTe commands:")
  (println "  :certify              | certify the" library-name "library (written in resources/cert)")
  (println "  :clear-cert           | clear the last certification (if any)")
  (println "  :axioms  [namespaces] | list all axioms in `namespaces`, or in whole " library-name "library if not specified")
  (println "  :help                 | this message"))

(defn run-certify! [library-name namespaces]
  (cert/certify-library! library-name namespaces))

(defn run-clear-cert! []
  (cert/clear-certification!))

(defn run-axioms! [args namespaces]
  ;; TODO: take args into account
  (let [axiom-map (into {} (map (fn [namesp]
                                  [namesp (map first (:axioms (u/fetch-ns-elements (the-ns namesp))))]) namespaces))]
    (println axiom-map))
  )


(defn -main [& args]
  (run-header)
  (if args
    (case (first args)
      ":certify" (run-certify! "core" ['latte.prop 'latte.equal 'latte.quant 'latte.classic 'latte.fun])
      ":clear-cert" (run-clear-cert!)
      ":axioms" (run-axioms! (rest args) ['latte.prop 'latte.equal 'latte.quant 'latte.classic 'latte.fun])
      ":help"
      ;; does not understand
      (do (println "==> Does not understand: " (first args))
          (run-doc "core")))
    (run-doc "core")))







