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

(declare match-list)
         
(defn match 
  ([patt term] (match {} patt term))
  ([env patt term]
   (cond
     (variable? patt) (assoc env patt term)
     (list? patt) (match-list env patt term)
     :else
     (if (= patt term)
       env
       false))))

(sequential? 'toto)
(sequential? '())
(list? 'toto)


(defn match-list [env patts terms]
  (if (seq patts)
    (if-not (list? terms)
      false
      (if (seq terms)
        (let [patt (first patts)
              term (first terms)]
          (if-let [env' (match env patt term)]
            (recur env' (rest patts) (rest terms))
            false))
        ;; no element in term
        false))
    ;; nothing left to match
    env))
      
(match '?X '(==> A A))
(match '==> '(==> A A))
(match '(==> A A) '(==> A A))
(match '(==> ?X ?Y) '(==> A A))


