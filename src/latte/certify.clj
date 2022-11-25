(ns latte.certify
  "Certification of LaTTe namespaces.
  The functions in this namespace allow to take a snapshot of
  the current running state of a namespace, and issue a certificate
  of all the theorems demonstrated (using a cryptographic signature scheme).
  This is a form of compilation for demonstrated theorems."
  
  (:require [digest]
            [latte.utils :as u]
            [clojure.string :as string]
            [clojure.java.io :as io]
            [clojure.edn :as edn]))

;; ====================
;; The signature scheme
;; ====================

;; thx: https://github.com/tebeka/clj-digest
(defn theorem-signature
  "Sign the specified theorem contents."
  [params type proof]
  (digest/sha-256 (str params "/" type "/" proof)))

;; ========================
;; The certificate database
;; ========================

(defonce +global-proof-certificate+ (atom {}))

(defn load-namespace-certificate!
  "Load the namespace named `namesp-name` certificate, if any."
  [namesp-name]
  (let [cert-dir (or (io/resource "cert")
                     (io/file "resources/cert"))
        namesp-fname (str namesp-name ".cert")
        namesp-file (or (io/resource (str "cert/" namesp-fname))
                        (io/file (str "resources/cert/" namesp-fname)))]
    ;;(println "[load-certificate] cert-dir=" cert-dir)
    ;;(println "[load-certificate] cert-file=" namesp-file)
    (if (or (nil? cert-dir) (nil? namesp-file) (and (instance? java.io.File namesp-file)
                                                    (not (.exists namesp-file))))
      ;; put an empty map for this namespace
      (swap! +global-proof-certificate+ #(assoc % namesp-name {}))
      ;; if there is a certification directory, try to find the correct certificate
      (let [thm-cert (edn/read-string (slurp (io/input-stream namesp-file)))]
        (swap! +global-proof-certificate+ #(assoc % namesp-name thm-cert))))))
        
(defn proof-certified?
  "Check if the provided proof is certified."
  [namesp thm-name thm-params thm-type thm-proof]
  (let [namesp-name (str namesp)
        namesp-cert (get @+global-proof-certificate+ namesp-name ::not-found)]
    (if (= namesp-cert ::not-found)
      (do (load-namespace-certificate! namesp-name)
          (recur namesp thm-name thm-params thm-type thm-proof))
      ;; found a certificate
      (let [thm-cert (get namesp-cert thm-name ::not-found)]
        (if (= thm-cert ::not-found)
          false
          ;; found a certificate
          (let [new-cert (theorem-signature thm-params thm-type thm-proof)]
            (= new-cert thm-cert)))))))

;; ===========================
;; The certification functions
;; ===========================

(def ^:dynamic *verbose-certification* true)

(defn mk-timestamp-file! [library-name]
  (when *verbose-certification*
    (println "..Generating certification timestamp")
    (println "  ==> library:" library-name))
  (let [timestamp (java.util.Date.)
        _ (when *verbose-certification* (println "  ==> date:" (str timestamp)))
        timestamp-filename "resources/cert/timestamp.edn"
        timestamp-file (io/file timestamp-filename)]
    ;; erase old timestamp file, if any
    (when (.exists timestamp-file)
      (when *verbose-certification* (println "  ==> deleting old timestamp file"))
      (io/delete-file timestamp-file))
    (when *verbose-certification*
      (println "  ==> write file:" (str "'" timestamp-filename "'")))
    ;; spit timestamp
    (spit timestamp-file {:library library-name
                          :timestamp timestamp })))

;; (mk-timestamp-file! "latte")

(defn clear-certification! []
  (when *verbose-certification*
    (println "..Clear certificate (cleaning up 'resource/cert' directory)"))
  (let [cert-dir (io/file "resources/cert")]
    (if (.exists cert-dir)
      (do (doseq [cert-file (.listFiles cert-dir)]
            (when *verbose-certification*
              (println "  ==> Deleting old certification file:" (.getName cert-file)))
            (.delete cert-file))
          ;; delete cert directory
          (when *verbose-certification*
            (println "  ==> Deleting old certification directory: " (.getName cert-dir)))
          (.delete cert-dir))
      ;; no cert directory
      (when *verbose-certification*
        (println "  ==> no certification directory")))))

;; (clear-certification!)

(defn demonstrated-theorems
  "Fetch a map of theorems with an actual proof in the namespace
  named `namesp' (a symbol). If not indicated the current namespace is used."
  ([namesp]
   (let [thms (:theorems (u/fetch-ns-elements (the-ns namesp)))]
     thms))
  ([] (demonstrated-theorems *ns*)))

;; (demonstrated-theorems 'latte-prelude.prop)

(defn certified-theorems
  "Build a map of theorem certifications from a map `thms' of theorems.
  Each theorem contents (definition ) is signed with "
  [thms]
  (into {} (reduce (fn [cthms [thm-name thm-content]]
                     (if (:proof thm-content)
                       (conj cthms [thm-name (theorem-signature (:params thm-content) (:type thm-content) (:proof thm-content))])
                       cthms)) [] thms)))

(defn certify-namespace! [namesp]
  (when *verbose-certification*
    ;;(println "..Certify namespace:" namesp)
    (println "  ==> Certification started ...")
    (flush))
  (if-let [thms (demonstrated-theorems namesp)]
    (let [thm-certs (certified-theorems thms)]
      (when *verbose-certification*
        (println "  ==> ... done all" (count thm-certs) "theorem(s) certified"))
      (let [cert-filename (str "resources/cert/" namesp ".cert")]
        (when *verbose-certification*
          (println "  ==> writing certification file:" cert-filename))
        (spit cert-filename thm-certs)
        (when *verbose-certification*
          (println "  ==> done"))))
    ;; no theorem
    (when *verbose-certification*
      (println "  ==> no theorem to certify (do nothing)"))))

;; (certify-namespace! 'latte.prop)

(defn certify-library! [library-name namespaces]
  (let [start-time (System/currentTimeMillis)]
    (when *verbose-certification*
      (println "=== Certifying library:" library-name)
      (println "  ==> namespaces:" namespaces "==="))
    ;; 1) clear the certificate
    (clear-certification!)
    ;; 2) create the certificate directory
    (let [cert-dir (io/file "resources/cert")]
      (.mkdir cert-dir)
      (when *verbose-certification*
        (println " ==> certification directory created"))
      ;; 3) create timestamp file
      (mk-timestamp-file! library-name)
      ;; 4) certify namespaces
      (doseq [namesp namespaces]
        (when *verbose-certification* 
          (println ".." (str "[" namesp "]"))
          (flush))
        (require namesp)
        (certify-namespace! namesp))
      (let [end-time (System/currentTimeMillis)]
        (println "=== Certificate issued in" (str (/ (- end-time start-time) 1000.0)  "s") "==")))))
