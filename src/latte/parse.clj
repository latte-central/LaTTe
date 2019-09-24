;;{
;; # Parsing tools
;;
;; In this namespace all the user-facing syntactic artefacts of LaTTe
;; are checked for well-formedness. This is not concerned with term-level parsing.
;; The emphasis is on precision and clarity of (potential) error messages
;;}

(ns latte.parse
  (:require [latte-kernel.presyntax :as stx]))


(defn parse-definition [args]
  (if (< (count args) 3)
    [:ko "Definition form requires at least 3 arguments." {:nb-args (count args)}]
    (let [def-name (first args)
          [status msg infos] (check-def-name def-name)]
      (if (= status :ko)
        [status msg infos]
        (let [def-doc (if (string? (second args))
                        )])





