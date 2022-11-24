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

(comment
  (variable? '?)
  (variable? '?X)
  (variable? '?X*)
  (variable? '?X+)
)

(defn simple-variable? [v]
  (and (variable? v)
       (not (#{\* \+ \?} (last (name v))))))

(comment
  (simple-variable? '?)
  (simple-variable? '?X)
  (simple-variable? '?X*)
  (simple-variable? '?X+)
)


(defn star-variable? [v]
  (and (variable? v)
       (= (last (name v)) \*)))

(comment
  (star-variable? '?X)
  (star-variable? '?)
  (star-variable? '?*)
  (star-variable? '?X*)
  (star-variable? '?_*)
)

(defn ext-variable-name [sv]
  (let [svname (name sv)]
    (subs svname 1 (dec (count svname)))))

(comment
  (ext-variable-name '?*)
  (ext-variable-name '?X*)
  (ext-variable-name '?_*)
)

(defn ext-variable-sym [sv]
  (symbol (str "?" (ext-variable-name sv))))

(comment
  (ext-variable-sym '?X*)
  (ext-variable-sym '?*)
)

(defn opt-variable? [v]
  (and (variable? v)
       (= (last (name v)) \?)))

(comment
  (opt-variable? '?X)
  (opt-variable? '?)
  (opt-variable? '??)
  (opt-variable? '?X?)
  (opt-variable? '?_?)

  (ext-variable-name '??)
  (ext-variable-name '?X?)
  (ext-variable-name '?_?)
)

(defn plus-variable? [v]
  (and (variable? v)
       (= (last (name v)) \+)))

(comment
  (plus-variable? '?X)
  (plus-variable? '?)
  (plus-variable? '?+)
  (plus-variable? '?X+)
  (plus-variable? '?_+)
)

(comment
  (ext-variable-name '?+)
  (ext-variable-name '?X+)
  (ext-variable-name '?_+)
)

(defrecord Repeat [patt min max sol cont])

(declare match-repeat
         match-list
         match-var)
         
(defn match 
  ([patt term] (match {} patt term))
  ([env patt term]
   (cond
     (simple-variable? patt) (match-var env patt term)
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

(declare count-min-expected-terms
         match-star)

(defn match-list [env patts terms]
  (if (seq patts)
    (if (seq terms)
      (let [min-count (count-min-expected-terms patts)]
        (if (< (count terms) min-count)
          false ; not enough terms in list
          (let [patt (first patts)
                term (first terms)]
            (cond
              (opt-variable? patt)
              (if-let [env' (match env (ext-variable-sym patt) term)]
                (recur env' (rest patts) (rest terms))
                (recur env (rest patts) terms))

              (star-variable? patt)
              (do (when (get env (ext-variable-sym patt))
                    (throw (ex-info "Multiple occurrence of zero-or-many variable" {:variable patt                                                                          :env env})))
                  (let [[matches terms'] (match-star (ext-variable-sym patt) env terms)]
                    (recur (assoc env (ext-variable-sym patt) matches) (rest patts) terms')))
              
              (plus-variable? patt)
              (do (when (get env (ext-variable-sym patt))
                    (throw (ex-info "Multiple occurrence of one-or-many variable" {:variable patt                                                                          :env env})))
                  (let [[matches terms'] (match-star (ext-variable-sym patt) env terms)]
                    (if (zero? (count matches))
                      false ; not enough matches                     
                      (recur (assoc env (ext-variable-sym patt) matches) (rest patts) terms'))))

              :else ; other kind of pattern
              (if-let [env' (match env patt term)]
                (recur env' (rest patts) (rest terms))
                false)))))
      ;; no element in term
      false)
    ;; nothing left to match
    (if (seq terms)
      false ; unmatched terms
      env)))

(defn match-star [sv env terms]
  (loop [terms terms, matches []]
    (if (seq terms)              
      (if-let [env' (match env sv (first terms))]
        (recur (rest terms) (conj matches (get env' sv)))
        [matches terms])
      [matches terms])))

(defn count-min-expected-terms [patts]
  (loop [patts patts, count 0]
    (if (seq patts)
      (if (or (star-variable? (first patts))
              (opt-variable? (first patts)))
        (recur (rest patts) count)
        ;; otherwise count is incremented
        (recur (rest patts) (inc count)))
      ;; no more patterns
      count)))

(comment
  (count-min-expected-terms '(?X toto ?Y* ?Z+ 42 ?Z?))
)
 
(comment     
  (match '?X '(==> A A))
  (match '==> '(==> A A))
  (match '(==> ?X) '(==> A A))
  (match '(==> A A) '(==> A A))
  (match '(==> ?X ?Y) '(==> A A))
  (match '(==> ?X ?X) '(==> A A))
  (match '(==> ?X ?X) '(==> A B))

  (match '(==> ?X*) '(==> A B C))
  (match '(==> ?X* ?Y) '(==> A B C))

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


;; (search-theorem 'latte-prelude.prop '(==> (and ?X ?Y) (and ?Y ?X)))
;; (search-theorem 'latte-prelude.prop '(==> (==> ?X ?Y) ?Z ?T))
;; (search-theorem 'latte-prelude.prop '(==> ?X (not ?X) ?Y))



