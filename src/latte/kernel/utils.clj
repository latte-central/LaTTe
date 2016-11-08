(ns latte.kernel.utils
  (:require [clj-by.example :refer [example do-for-example]])
  )

(def ^:private +examples-enabled+)

(defn vconcat
  "Concatenates vectors `v1` and `v2`.
  (linear time)."
  [v1 v2]
  (loop [s v2, v v1]
    (if (seq s)
      (recur (rest s) (conj v (first s)))
      v)))

(example
 (vconcat [1 2 3] [4 5 6]) => [1 2 3 4 5 6])


(defn vcons
  "Conses element `e` in front of vector `v`.
   (linear time)"
  [e v]
  (vconcat [e] v))

(example
 (vcons 1 [2 3 4]) => [1 2 3 4])

(defn pair? [v]
  (and (vector v)
       (= (count v) 2)))

(defn vectorn? [v n]
  (and (vector v)
       (= (rem (count v) n) 0)))

(example
 (vectorn? [1 2 3 4] 4) => true)


(example
 (vectorn? [1 2 3 4 5 6 7 8] 4) => true)

(example
 (vectorn? [1 2 3 4 5 6 7] 4) => false)

(defn safe-get
  "A safe(r) variant of `get` for collections with non-`nil` keys."
  [coll key]
  (if-let [val (get coll key)]
    val
    (throw (ex-info "No such value is collection" {:coll coll :key key}))))




