
;;{
;;
;; # Utilities : association lists
;;
;; Clojure does not support association lists
;; out of the box, whereas it is an important
;; data-structure for scoped lexical environments.
;;
;;}

(ns latte.alist
  (:refer-clojure :exclude [assoc])
  (:require [latte.utils :refer [example]]))

(def ^:dynamic *examples-enabled* true)

(defn acons
  "Construct an association for `key` to `val`
  in `alist`."
  [key val alist]
  (conj alist [key val]))

(example (acons 'a 1
                (acons 'b 2
                       (acons 'c 3
                              (acons 'b 4 '()))))
         => '([a 1] [b 2] [c 3] [b 4]))

(defn assoc
  "Fetch the binding corresponding to `key` in `alist`. 
  Returns `nil` in every other situations."
  [key alist]
  (if (seq alist)
    (let [binding (first alist)]
      (if (= key (first binding))
        binding
        (recur key (rest alist))))
    nil))

(example (assoc 'b '([a 1] [b 2] [c 3] [b 4])) => ['b 2])

(example (assoc 'd '([a 1] [b 2] [c 3] [b 4])) => nil)

(defn vassoc
  "Fetch the value corresponding to `key` in `alist`. 
  Return `nil` or the optional `default` argument."
  ([key alist default]
   (let [binding (assoc key alist)]
     (if binding
       (second binding)
       default)))
  ([key alist] (vassoc key alist nil)))

(example (vassoc 'b '([a 1] [b 2] [c 3] [b 4])) => 2)

(example (vassoc 'd '([a 1] [b 2] [c 3] [b 4])) => nil)

(example (vassoc 'd '([a 1] [b 2] [c 3] [b 4]) 'not-found) => 'not-found)







