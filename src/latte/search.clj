(ns latte.search
  "A Search facility for LaTTe
  (searching theorems, definitions, etc.)
  "

  (:require [latte-prelude.prop :as p]
            [latte.utils :as u])
)

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
 
(comment     
  (match '?X '(==> A A))
  (match '==> '(==> A A))
  (match '(==> ?X) '(==> A A))
  (match '(==> A A) '(==> A A))
  (match '(==> ?X ?Y) '(==> A A))
  (match '(==> ?X ?X) '(==> A A))
  (match '(==> ?X ?X) '(==> A B))
  )


;; XXX: defonce when finalized ?
(def +search-namespaces+ (atom {}))

(defn namespace? [thing]
  (instance? clojure.lang.Namespace thing))

(defn register-search-namespace! [arg]
  (cond 
    (symbol? arg)
    (if-let [ns-arg (find-ns arg)]
      (recur ns-arg)
      (throw (ex-info "Cannot register search namespace: not found" {:namespace arg})))
    
    (namespace? arg)
    (do (swap! +search-namespaces+ assoc (ns-name arg) arg)
        [:registered (ns-name arg)])

    :else
    (throw (ex-info "Cannot register search namespace: wrong argument" {:arg arg}))))
    
(register-search-namespace! 'latte-prelude.prop)

@+search-namespaces+

(defn search-theorem
  ([things patt results]
   (if (seq things)
     (cond
       ;; a namespace name
       (symbol? (first things))
       (if-let [search-ns (get @+search-namespaces+ (first things))]
         (recur (cons search-ns (rest things)) patt results)
         (throw (ex-info "Cannot search pattern: no such registered namespace" {:namespace (first things)})))

       ;; a namespace
       (namespace? (first things))
       (let [elems (u/fetch-ns-elements (first things))]
         (if-let [thms (get elems :theorems)]
           (recur (concat (map (fn [[thm-name _]]
                                          (ns-resolve (first things) thm-name)) thms)
                                   (rest things)) patt results)
           (recur (rest things) patt results)))

       ;; a var, hence a theorem
       (var? (first things))
       (if-let [body (get (meta (first things)) :body)]
         (if-let [env (match patt body)]
           (recur (rest things) patt (conj results [(first things) env]))
           (recur (rest things) patt results)))

       :else
       (throw (ex-info "Cannot search pattern: unexpected argument" {:arg things})))
     ;; no more things to search
     results))
  ([ns-names patt]
   (if (seqable? ns-names) 
     (search-theorem ns-names patt [])
     (search-theorem (list ns-names) patt [])))
  ([patt] (search-theorem (into #{} (map second @+search-namespaces+)) patt)))


           

