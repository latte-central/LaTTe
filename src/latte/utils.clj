(ns latte.utils
  "Misc. utilities for LaTTe libraries."
  (:require [latte-kernel.defenv :as defenv]
            [latte-kernel.norm :as norm]))

;; decomposer (rebindable) parameters
(def ^:dynamic *decomposer-performs-delta-steps* true)
(def ^:dynamic *decomposer-performs-norm* true)

(defn decomposer
  ([decompose-fn def-env ctx term] (decomposer decompose-fn def-env ctx term true true))
  ([decompose-fn def-env ctx term try-delta? try-norm?]
   (let [[status res]
         (try [:ok (decompose-fn term)]
              (catch Exception e
                [:ko e]))]
     (if (= status :ok)
       res
       (let [[term' rcount] (if (and *decomposer-performs-delta-steps* try-delta?)
                              (norm/delta-step def-env ctx term)
                              [term 0])]
         (if (pos? rcount)
           (recur decompose-fn def-env ctx term' false try-norm?)
           (if (and *decomposer-performs-norm* try-norm?)
             (let [term' (norm/normalize def-env ctx term)]
               (recur decompose-fn def-env ctx term' false false))
             (throw res))))))))


(defn set-opacity! [defvar flag]
  "Equality is most of the time handled in an opaque way, but it
is sometimes required to handle it transparently. This function
 should be used in this case."
  (alter-var-root defvar (fn [eq]
                           (update eq :opts (fn [opts] (assoc opts :opaque flag))))))


(defn fetch-ns-elements
  "Fetch the LaTTe elements in specified `ns` (or the current namespace by default)."
  ([] (fetch-ns-elements *ns*))
  ([ns] (let [defs (ns-map ns)
              ;; some cleanups
              defs (into {}
                         (filter #(and (not (clojure.string/starts-with? (str (second %)) "#'clojure."))
                                       (var? (second %))) defs))]
          (reduce (fn [elems [ename evar]]
                    (let [elem (var-get evar)]
                      (cond
                        (defenv/definition? elem)
                        (assoc-in elems [:definitions ename] elem)
                        (defenv/theorem? elem)
                        (assoc-in elems [:theorems ename] elem)
                        (defenv/axiom? elem)
                        (assoc-in elems [:axioms ename] elem)
                        (defenv/notation? elem)
                        (assoc-in elems [:notations ename] elem)
                        (defenv/implicit? elem)
                        (assoc-in elems [:implicits ename] elem)
                        :else elems)))
                  {:theorems {}
                   :definitions {}
                   :axioms {}
                   :notations {}
                   :implicits {}} defs))))

