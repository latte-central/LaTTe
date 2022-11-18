(ns latte.search
  "A Search facility for LaTTe
  (searching theorems, definitions, etc.)
  "

  (:require [latte-prelude.prop :as p])
)

(meta #'p/impl-refl)

(defn variable? [v]
  (if-not (symbol? v)
    false
    (let [sname (name v)]
      (and (> (count sname) 1)
           (= (first sname) \?)))))

(declare match-list
         match-var)
         
(defn match 
  ([patt term] (match {} patt term))
  ([env patt term]
   (cond
     (variable? patt) (match-var env patt term)
     (list? patt) (if-not (list? term)
                    false
                    (match-list env patt term))
     :else
     (if (= patt term)
       env
       false))))

(defn match-var [env var term]
  (if-let [prev-term (get env var)]
    (if (= prev-term term)
      env
      false)
    ;; no previous binding
    (assoc env var term)))

(defn match-list [env patts terms]
  (if (seq patts)
    (if (seq terms)
      (let [patt (first patts)
            term (first terms)]
        (if-let [env' (match env patt term)]
          (recur env' (rest patts) (rest terms))
          false))
      ;; no element in term
      false)
    ;; nothing left to match
    (if (seq terms)
      false ; unmatched terms
      env)))
      
(match '?X '(==> A A))
(match '==> '(==> A A))
(match '(==> ?X) '(==> A A))
(match '(==> A A) '(==> A A))
(match '(==> ?X ?Y) '(==> A A))
(match '(==> ?X ?X) '(==> A A))
(match '(==> ?X ?X) '(==> A B))



