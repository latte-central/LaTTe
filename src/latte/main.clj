(ns latte.main
  "The entry point for LaTTe as a standalone tool.
  This is mainly for certifying the core library (target `certify`)
  but other functionalities are provided, like listing axioms, etc."

  (:require [latte.utils :as u]            
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
  (println "  :axioms  [namespaces] | list all axioms in `namespaces`, or in whole" library-name "library if not specified")
  (println "  :help                 | this message"))

(defn require-all! [namespaces]
  (doseq [namesp namespaces]
         (require namesp)))

(defn run-certify! [library-name namespaces]
  ;;(require-all! namespaces)
  (cert/certify-library! library-name namespaces))

(defn run-clear-cert! []
  (cert/clear-certification!))

(defn run-axioms! [args namespaces]
  ;; TODO: take args into account
  (require-all! namespaces)
  (let [axiom-map (into {} (map (fn [namesp]
                                  [namesp (map first (:axioms (u/fetch-ns-elements (the-ns namesp))))]) namespaces))]
    (println axiom-map))
  )


(defn latte-main [args library-name namespaces]
  (run-header)
  (if args
    (case (first args)
      ":certify" (run-certify! library-name namespaces)
      ":clear-cert" (run-clear-cert!)
      ":axioms" (run-axioms! (rest args) namespaces)
      ":help"
      ;; does not understand
      (do (println "==> Does not understand: " (first args))
          (run-doc library-name)))
    (run-doc "core")))


