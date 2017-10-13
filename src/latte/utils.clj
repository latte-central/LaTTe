(ns latte.utils
  "Misc. utilities for LaTTe libraries."
  (:require [latte-kernel.norm :as norm]))

;; decomposer (rebindable) parameters
(def ^:dynamic *decomposer-performs-delta-steps* true)
(def ^:dynamic *decomposer-performs-norm* true)

(defn decomposer
  ([decompose-fn def-env ctx term] (decomposer decompose-fn def-env ctx term true))
  ([decompose-fn def-env ctx term retry?]
   (let [[status res]
         (try [:ok (decompose-fn term)]
              (catch Exception e
                [:ko e]))]
     (if (= status :ok)
       res
       (if retry?
         (let [[term' ok?] (if *decomposer-performs-delta-steps*
                             (norm/delta-step def-env ctx term)
                             [term false])]
           (if ok?
             (recur decompose-fn def-env ctx term' true)
             (if *decomposer-performs-norm*
               (let [term' (norm/normalize def-env ctx term)]
                 (recur decompose-fn def-env ctx term' false))
               (throw res))))
         ;; no retry
         (throw res))))))


