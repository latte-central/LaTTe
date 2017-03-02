(ns latte.kernel.norm
  "Normalization and equivalence."

  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.utils :as utils :refer [vconcat]]
            [latte.kernel.syntax :as stx]
            [latte.kernel.defenv :as defenv :refer [definition? theorem? axiom? special?]]))


;;{
;; # Normalization
;;}

(def ^:private +examples-enabled+)

;;{
;; ## Beta-reduction

;; a tricky example :
;;  ((lambda [z :type] (lambda [x :type] (x y))) x)
;;   ~~> (lambda [x :type] (x x)    is wrong
;;
;;   ((lambda [z :type] (lambda [x :type] (x z))) x)
;; = ((lambda [z :type] (lambda [y :type] (y z))) x)
;;   ~~> (lambda [y :type] (y x)    is correct
;;}

(defn redex? [t]
  (and (stx/app? t)
       (stx/lambda? (first t))))

(example
 (redex? '[(λ [x ✳] x) y]) => true)

(defn beta-reduction [t]
  (if (redex? t)
    (let [[[_ [x _] body] rand] t]
      (stx/subst body x rand))
    (throw (ex-info "Cannot beta-reduce. Not a redex" {:term t}))))

(example
 (beta-reduction '[(λ [x ✳] [x x]) y])
 => '[y y])


(declare beta-step)

(defn beta-step-args [ts]
  (loop [ts ts, ts' [], red? false]
    (if (seq ts)
      (let [[t' red-1?] (beta-step (first ts))]
        (recur (rest ts) (conj ts' t') (or red? red-1?)))
      [ts' red?])))

(defn beta-step [t]
  (cond
    ;; binder
    (stx/binder? t)
    (let [[binder [x ty] body] t
          ;; 1) try reduction in binding type
          [ty' red-1?] (beta-step ty)
          ;; 2) also try reduction in body
          [body' red-2?] (beta-step body)]
      [(list binder [x ty'] body') (or red-1? red-2?)])
    ;; application
    (stx/app? t)
    (let [[left right] t
          ;; 1) try left reduction
          [left' lred?] (beta-step left)
          ;; 2) also try right reduction
          [right' rred?] (beta-step right)]
      (if (stx/lambda? left')
        ;; we have a redex
        [(beta-reduction [left' right']) true]
        ;; or we stay with an application
        [[left' right'] (or lred? rred?)]))
    ;; reference
    (stx/ref? t)
    (let [[def-name & args] t
          [args' red?] (beta-step-args args)
          t' (if red? (list* def-name args') t)]
      [t' red?])
    ;; other cases
    :else [t false]))

(defn beta-red [t]
  (let [[t' _] (beta-step t)]
    t'))

(example
 (beta-red '[(λ [x ✳] x) y]) => 'y)

(example
 (beta-red '[[(λ [x ✳] x) y] z]) => '[y z])

(example
 (beta-red '(λ [y [(λ [x □] x) ✳]] y))
 => '(λ [y ✳] y))

(example
 (beta-red '[z [(λ [x ✳] x) y]]) => '[z y])

(example
 (beta-red '[x y]) => '[x y])

;;{
;; ## Delta-reduction (unfolding of definitions)
;;}

(defn instantiate-def [params body args]
  ;;(println "[instantiate-def] params=" params "body=" body "args=" args)
  (loop [args args, params params, sub {}]
    (if (seq args)
      (if (empty? params)
        (throw (ex-info "Not enough parameters (please report)" {:args args}))
        (recur (rest args) (rest params) (assoc sub (ffirst params) (first args))))
      (loop [params (reverse params), res body]
        (if (seq params)
          (recur (rest params) (list 'λ (first params) res))
          (stx/subst res sub))))))

(example
 (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                  '[[x y] [z x]]
                  '((λ [t ✳] t) t1 [t2 t3]))
 => '[[(λ [t ✳] t) t1] [[t2 t3] (λ [t ✳] t)]])

(example
 (instantiate-def '[[x ✳] [y ✳] [z ✳] [t ✳]]
                  '[[x y] [z t]]
                  '((λ [t ✳] t) t1 [t2 t3]))
 => '(λ [t' ✳] [[(λ [t ✳] t) t1] [[t2 t3] t']]))

(example
 (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                  '[[x y] z]
                  '())
 => '(λ [x ✳] (λ [y ✳] (λ [z ✳] [[x y] z]))))

(defn delta-reduction
  ([def-env t] (delta-reduction def-env t false))
  ([def-env t local?]
   ;; (println "[delta-reduction] t=" t)
   (if (not (stx/ref? t))
     (throw (ex-info "Cannot delta-reduce: not a reference term (please report)." {:term t}))
     (let [[name & args] t
           [status sdef] (if local?
                           (if-let [sdef (get def-env name)]
                             [:ok sdef]
                             [:ko nil])
                           (defenv/fetch-definition def-env name))]
       ;; (println "[delta-reduction] term=" t "def=" sdef)
       (if (= status :ko)
         [t false] ;; No error?  or (throw (ex-info "No such definition" {:term t :def-name name}))
         (if (> (count args) (:arity sdef))
           (throw (ex-info "Too many arguments to instantiate definition." {:term t :def-name name :nb-params (count (:arity sdef)) :nb-args (count args)}))
           (cond
            (definition? sdef)
            ;; unfolding a defined term
            (if (:parsed-term sdef)
              [(instantiate-def (:params sdef) (:parsed-term sdef) args) true]
              (throw (ex-info "Cannot unfold term reference (please report)"
                              {:term t :def sdef})))
            (theorem? sdef)
            (if (:proof sdef)
              ;; unfolding works but yields very big terms
              ;; having a proof is like a certicate and thus
              ;; the theorem can now be considered as an abstraction, like
              ;; an axiom but with a proof...
              ;; [(instantiate-def (:params sdef) (:proof sdef) args) true]
              [t false]
              (throw (ex-info "Cannot use theorem with no proof." {:term t :theorem sdef})))
            (axiom? sdef) [t false]
            (special? sdef)
            (throw (ex-info "Specials must not exist at delta-reduction time (please report)" {:term t :special sdef}))
            ;; XXX: before that, specials were handled by delta-reduction
            ;; (if (< (count args) (:arity sdef))
            ;;   (throw (ex-info "Not enough argument for special definition." { :term t :arity (:arity sdef)}))
            ;;   (let [term (apply (:special-fn sdef) def-env ctx args)]
            ;;     [term true]))
            :else (throw (ex-info "Not a Latte definition (please report)." {:term t :def sdef})))))))))

(example
 (delta-reduction {'test (defenv/map->Definition
                          '{:name test
                            :arity 3
                            :params [[x ✳] [y □] [z ✳]]
                            :parsed-term [y (λ [t ✳] [x [z t]])]})}
                  '(test [a b] c [t (λ [t] t)]))
 => '[[c (λ [t' ✳] [[a b] [[t (λ [t] t)] t']])] true])

(example
 (delta-reduction {'test (defenv/map->Theorem
                          '{:name test
                            :arity 3
                            :params [[x ✳] [y □] [z ✳]]
                            :proof [y (λ [t ✳] [x [z t]])]})}
                  '(test [a b] c [t (λ [t] t)]))
 => '[(test [a b] c [t (λ [t] t)]) false])
 ;;=> '[[c (λ [t' ✳] [[a b] [[t (λ [t] t)] t']])] true])

(example
 (delta-reduction {'test (defenv/map->Axiom
                          '{:arity 3
                            :tag :axiom
                            :params [[x ✳] [y □] [z ✳]]})}
                   '(test [a b] c [t (λ [t] t)]))
 => '[(test [a b] c [t (λ [t] t)]) false])

(example
 (delta-reduction {'test (defenv/map->Definition
                          '{:arity 3
                            :tag :definition
                            :params [[x ✳] [y □] [z ✳]]
                            :parsed-term [y (λ [t ✳] [x [z t]])]})}
                  '(test [a b] c))
 => '[(λ [z ✳] [c (λ [t ✳] [[a b] [z t]])]) true])

(declare delta-step)

(defn delta-step-args [def-env ts local?]
  (loop [ts ts, ts' [], red? false]
    (if (seq ts)
      (let [[t' red-1?] (delta-step def-env (first ts) local?)]
        (recur (rest ts) (conj ts' t') (or red? red-1?)))
      [ts' red?])))

(defn delta-step
  ([def-env t] (delta-step def-env t false))
  ([def-env t local?]
   ;; (println "[delta-step] t=" t)
   (cond
     ;; binder
     (stx/binder? t)
     (let [[binder [x ty] body] t
           ;; 1) try reduction in binding type
           [ty' red1?] (delta-step def-env ty local?)
           ;; 2) also try reduction in body
           [body' red2?] (delta-step def-env body local?)]
       [(list binder [x ty'] body') (or red1? red2?)])
     ;; application
     (stx/app? t)
     (let [[left right] t
           ;; 1) try left reduction
           [left' lred?] (delta-step def-env left local?)
           ;; 2) also try right reduction
           [right' rred?] (delta-step def-env right local?)]
       [[left' right'] (or lred? rred?)])
     ;; reference
     (stx/ref? t)
     (let [[def-name & args] t
           [args' red1?] (delta-step-args def-env args local?)
           t' (if red1? (list* def-name args') t)
           [t'' red2?] (delta-reduction def-env t' local?)]
       [t'' (or red1? red2?)])
     ;; other cases
     :else [t false])))

(example
 (delta-step {} 'x) => '[x false])

(example
 (delta-step {'test (defenv/map->Definition
                     '{:arity 1
                       :tag :definition
                       :params [[x ✳]]
                       :parsed-term [x x]})}
             '[y (test [t t])])
 => '[[y [[t t] [t t]]] true])

(example
 (delta-step {'test (defenv/map->Definition
                     '{:arity 2
                       :tag :definition
                       :params [[x ✳] [y ✳]]
                       :parsed-term [x [y x]]})}
             '[y (test [t t] u)])
 => '[[y [[t t] [u [t t]]]] true])

;;{
;; ## Reduction of specials
;;}

(defn special-reduction [def-env ctx t]
  ;; (println "[special-reduction] t=" t)
  (if (not (stx/ref? t))
    (throw (ex-info "Cannot special-reduce: not a reference term." {:term t}))
    (let [[name & args] t
          [status sdef] (defenv/fetch-definition def-env name)]
      (if (= status :ko)
        [t false] ;; No error?  or (throw (ex-info "No such definition" {:term t :def-name name}))
        ;;(if (> (count args) (:arity sdef))
          ;;(throw (ex-info "Too many arguments to instantiate special." {:term t :def-name name :nb-params (count (:arity sdef)) :nb-args (count args)}))
          (if (special? sdef)
            ;;(if (< (count args) (:arity sdef))
            ;;(throw (ex-info "Not enough argument for special definition." { :term t :arity (:arity sdef)}))
            (do
              ;; (println "[special-reduction] sdef=" sdef)
              (let [term (apply (:special-fn sdef) def-env ctx args)]
                [term true])) ;;)
            [t false])))))
;;)

(declare special-step)

(defn special-step-args [def-env ctx ts]
  (loop [ts ts, ts' [], red? false]
    (if (seq ts)
      (let [[t' red1?] (special-step def-env ctx (first ts))]
        (recur (rest ts) (conj ts' t') (or red? red1?)))
      [ts' red?])))

(defn special-step [def-env ctx t]
  ;; (println "[delta-step] t=" t)
  (cond
    ;; binder
    (stx/binder? t)
    (let [[binder [x ty] body] t]
      ;; 1) try reduction in binding type
      (let [[ty' red1?] (special-step def-env ctx ty)
            ;; 2) try reduction in body
            [body' red2?] (special-step def-env ctx body)]
        [(list binder [x ty'] body') (or red1? red2?)]))
    ;; application
    (stx/app? t)
    (let [[left right] t
          ;; 1) try left reduction
          [left' lred?] (special-step def-env ctx left)
          ;; 2) try right reduction
          [right' rred?] (special-step def-env ctx right)]
      [[left' right'] (or lred? rred?)])
    ;; reference
    (stx/ref? t)
    (let [[def-name & args] t
          [args' red1?] (special-step-args def-env ctx args)
          t' (if red1? (list* def-name args') t)
          [t'' red2?] (special-reduction def-env ctx t')]
      [t'' (or red1? red2?)])
    ;; other cases
    :else [t false]))

(defn special-normalize [def-env ctx t]
  (let [[t' red?] (special-step def-env ctx t)]
    (if red?
      (recur def-env ctx t')
      t')))

;;{
;; ## Normalization (up-to beta/delta)
;;}

(defn beta-normalize [t]
  (let [[t' red?] (beta-step t)]
    (if red?
      (recur t')
      t')))

(defn delta-normalize [def-env t]
  (let [[t' red?] (delta-step def-env t)]
    (if red?
      (recur def-env t')
      t')))

(defn delta-normalize-local [def-env t]
  (let [[t' red?] (delta-step def-env t true)]
    (if red?
      (recur def-env t')
      t')))

;; XXX : this is a critical function... need to be checked
(defn beta-delta-special-normalize [def-env ctx t]
  ;;(println "[beta-delta-special-normalize]: t=" t)
  (let [[t' spec-red?] (special-step def-env ctx t)]
    (if spec-red?
      (do ;;(println "  [special] t ==> " t')
          (recur def-env ctx t'))
      (let [[t' delta-red?] (delta-step def-env t)]
        (if delta-red?
          (do ;;(println "  [delta] t ==> " t')
              (recur def-env ctx t'))
          (let [[t' beta-red?] (beta-step t)]
            (if beta-red?
              (do ;;(println "  [beta] t ==> " t')
                  (recur def-env ctx t'))
              t')))))))

(defn normalize
  ([t] (normalize {} [] t))
  ([def-env t] (normalize def-env [] t))
  ([def-env ctx t] (beta-delta-special-normalize def-env ctx t)))

(example
 (normalize '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))
 => '(λ [y ✳] y))

(defn beta-eq?
  "TODO arguably it might be better to have around only the three paramter
  version of normalize: (normalize def-env ctx t)."
  ([t1 t2]
   (let [t1' (normalize t1)
         t2' (normalize t2)]
     (stx/alpha-eq? t1' t2')))
  ([def-env t1 t2]
   (let [t1' (normalize def-env t1)
         t2' (normalize def-env t2)]
     (stx/alpha-eq? t1' t2')))
  ([def-env ctx t1 t2]
   (let [t1' (normalize def-env ctx t1)
         t2' (normalize def-env ctx t2)]
     (stx/alpha-eq? t1' t2')))
  ([def-env ctx t1 t2 & more]
   (apply stx/alpha-eq? (map #(normalize def-env ctx %)
                             (vector t1 t2 more)))))

(example
 (beta-eq? '(λ [z ✳] z)
           '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y])) => true)

(example
 (beta-eq? '(λ [z ✳] z)
           '(λ [x ✳] x)
           '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y])) => true)
