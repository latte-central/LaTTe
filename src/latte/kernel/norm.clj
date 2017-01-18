(ns latte.kernel.norm
  "Normalization and equivalence."

  (:require [clj-by.example :refer [example do-for-example]]
            [latte.kernel.utils :as utils :refer [vconcat]]
            [latte.kernel.presyntax :as parser]
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

(defn redex? [t]
  (and (stx/app? t)
       (stx/lambda? (:left t))))

(example
 (redex? (parser/parse '((λ [x ✳] x) y))) => true)

(defn beta-reduction [t]
  (if (redex? t)
    (stx/apply-to (:body (:left t)) (:right t))
    (throw (ex-info "Cannot beta-reduce. Not a redex" {:term t}))))

(example
 (stx/unparse-ln (beta-reduction (parser/parse '((λ [x ✳] (x x)) y))))
 => '(y y))

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
    (let [;; 1) try reduction in binding type
          [ty red-1?] (beta-step (:type t))
          ;; 2) also try reduction in body
          [body red-2?] (beta-step (:body t))]
      [((stx/binder-fn t) (:name t) ty body) (or red-1? red-2?)])
    ;; application
    (stx/app? t)
    (let [;; 1) try left reduction
          [left' lred?] (beta-step (:left t))
          ;; 2) also try right reduction
          [right' rred?] (beta-step (:right t))]
      (if (stx/lambda? left')
        ;; we have a redex
        [(beta-reduction (stx/mk-app left' right')) true]
        ;; or we stay with an application
        [(stx/mk-app left' right') (or lred? rred?)]))
    ;; reference
    (stx/ref? t)
    (let [[args' red?] (beta-step-args (:args t))
          t' (if red? (stx/mk-ref (:name t) args') t)]
      [t' red?])
    ;; other cases
    :else [t false]))

(defn beta-red [t]
  (let [[t' _] (beta-step t)]
    t'))

(example
 (stx/unparse-ln
  (beta-red (parser/parse '((λ [x ✳] x) y))))
 => 'y)

(example
 (stx/unparse-ln
  (beta-red (parser/parse '(((λ [x ✳] x) y) z))))
 => '(y z))

(example
 (stx/unparse-ln
  (beta-red (parser/parse '(λ [y [(λ [x □] x) ✳]] y))))
 => '(λ [✳] :0))

(example
 (stx/unparse-ln
  (beta-red (parser/parse '[z [(λ [x ✳] x) y]])))
 => '(z y))

(example
 (stx/unparse-ln
  (beta-red (parser/parse '(x y))))
 => '(x y))

;;{
;; ## Delta-reduction (unfolding of definitions)
;;}

(defn instantiate-def [params body args]
  ;; (println "[instantiate-def] params=" params "body=" body "args=" args)
  (loop [args args, params params, sub {}]
    (if (seq args)
      (if (empty? params)
        (throw (ex-info "Not enough parameters (please report)" {:args args}))
        (recur (rest args) (rest params) (assoc sub (ffirst params) (first args))))
      ;; no more arguments
      (loop [params (reverse params), res body]
        (if (seq params)
          (recur (rest params) (stx/mk-lambda (ffirst params) (second (first params)) (stx/close res (ffirst params))))
          (do
            ;; (println "[instantiate-def] sub=" sub)
            (stx/subst res sub)))))))

(example
 (stx/unparse-ln
  (instantiate-def '[[x ✳] [y ✳] [z ✳]] 
                   (parser/parse '((x y) (z x)))
                   (mapv parser/parse
                         '[(λ [t ✳] t)
                           t1
                           [t2 t3]])))
 => '((λ [✳] :0) t1 (t2 t3 (λ [✳] :0))))

(example
 (stx/unparse-ln
  (instantiate-def '[[x ✳] [y ✳] [z ✳] [t ✳]]
                   (parser/parse '((x y) (z t)))
                   (mapv parser/parse
                         '[(λ [t ✳] t)
                           t1
                           [t2 t3]])))
 => '(λ [✳] ((λ [✳] :0) t1 (t2 t3 :0))))

(example
 (stx/unparse-ln
  (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                   (parser/parse '[[x y] z])
                   '()))
 => '(λ [✳] (λ [✳] (λ [✳] (:2 :1 :0)))))

(defn delta-reduction
  ([def-env t] (delta-reduction def-env t false))
  ([def-env t local?]
   ;; (println "[delta-reduction] t=" t)
   (if (not (stx/ref? t))
     (throw (ex-info "Cannot delta-reduce: not a reference term (please report)." {:term t}))
     (let [[status sdef] (if local?
                           (if-let [sdef (get def-env (:name t))]
                             [:ok sdef]
                             [:ko nil])
                           (defenv/fetch-definition def-env (:name t)))]
       ;; (println "[delta-reduction] term=" t "def=" sdef)
       (if (= status :ko)
         [t false] ;; No error?  or (throw (ex-info "No such definition" {:term t :def-name name}))
         (if (> (count (:args t)) (:arity sdef))
           (throw (ex-info "Too many arguments to instantiate definition." {:term t :def-name (:name t) :nb-params (count (:arity sdef)) :nb-args (count (:args t))}))
           (cond
            (definition? sdef)
            ;; unfolding a defined term
            (if (:parsed-term sdef)
              [(instantiate-def (:params sdef) (:parsed-term sdef) (:args t)) true]
              (throw (ex-info "Cannot unfold term reference (please report)"
                              {:term t :def sdef})))
            (theorem? sdef)
            (if (:proof sdef)
              ;; unfolding works but yields very big terms
              ;; having a proof is like a certicate and thus
              ;; the theorem can now be considered as an abstraction, like
              ;; an axiom but with a proof...
              ;; [(instantiate-def (:params sdef) (:proof sdef) (:args t)) true]
              [t false]
              (throw (ex-info "Cannot use theorem with no proof." {:term t :theorem sdef})))
            (axiom? sdef) [t false]
            (special? sdef)
            (throw (ex-info "Specials must not exist at delta-reduction time (please report)" {:term t :special sdef}))
            ;; XXX: before that, specials were handled by delta-reduction
            ;; (if (< (count (:args t)) (:arity sdef))
            ;;   (throw (ex-info "Not enough argument for special definition." { :term t :arity (:arity sdef)}))
            ;;   (let [term (apply (:special-fn sdef) def-env ctx (:args t))]
            ;;     [term true]))
            :else (throw (ex-info "Not a Latte definition (please report)." {:term t :def sdef})))))))))

(example
 (stx/unparse-ln
  (first
   (let [def-env {'test
                  (defenv/map->Definition
                    {:name test
                     :arity 3
                     :params '[[x ✳] [y □] [z ✳]]
                     :parsed-term (parser/parse '(y (λ [t ✳] [x [z t]])))})}]
     (delta-reduction def-env
                      (parser/parse def-env '(test (a b) c (t (λ [t :type] t))))))))
 => '(c (λ [✳] (a b (t (λ [✳] :0) :0)))))

(example
 (stx/unparse-ln
  (first
   (let [def-env {'test (defenv/map->Theorem
                          {:name test
                           :arity 3
                           :params '[[x ✳] [y □] [z ✳]]
                           :proof (parser/parse '[y (λ [t ✳] [x [z t]])])})}]
     (delta-reduction def-env
                      (parser/parse def-env '(test [a b] c [t (λ [t :type] t)]))))))
 => '(test (a b) c (t (λ [✳] :0))))

(example
  (stx/unparse-ln
  (first
   (let [def-env {'test (defenv/map->Axiom
                          {:name test
                           :arity 3
                           :params '[[x ✳] [y □] [z ✳]]
                           :proof (parser/parse '[y (λ [t ✳] [x [z t]])])})}]
     (delta-reduction def-env
                      (parser/parse def-env '(test [a b] c [t (λ [t :type] t)]))))))
 => '(test (a b) c (t (λ [✳] :0))))

(example
 (stx/unparse-ln
  (first
   (let [def-env {'test (defenv/map->Definition
                          {:arity 3
                           :tag :definition
                           :params '[[x ✳] [y □] [z ✳]]
                           :parsed-term (parser/parse '[y (λ [t ✳] [x [z t]])])})}]
     (delta-reduction def-env
                      (parser/parse def-env '(test [a b] c))))))
 => '(λ [✳] (c (λ [✳] (a b (:1 :0)))))) 

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
     (let [;; 1) try reduction in binding type
           [ty red1?] (delta-step def-env (:type t) local?)
           ;; 2) also try reduction in body
           [body red2?] (delta-step def-env (:body t) local?)]
       [((stx/binder-fn t) (:name t) ty body) (or red1? red2?)])
     ;; application
     (stx/app? t)
     (let [;; 1) try left reduction
           [left lred?] (delta-step def-env (:left t) local?)
           ;; 2) also try right reduction
           [right rred?] (delta-step def-env (:right t) local?)]
       [(stx/mk-app left right) (or lred? rred?)])
     ;; reference
     (stx/ref? t)
     (let [[args red1?] (delta-step-args def-env (:args t) local?)
           t' (if red1? (stx/mk-ref (:name t) args) t)
           [t'' red2?] (delta-reduction def-env t' local?)]
       [t'' (or red1? red2?)])
     ;; other cases
     :else [t false])))

(example
 (delta-step {} (parser/parse 'x)) => [(stx/mk-fvar 'x) false])

(example
 (stx/unparse-ln
  (first
   (let [def-env {'test (defenv/map->Definition
                          {:arity 1
                           :tag :definition
                           :params '[[x ✳]]
                           :parsed-term (parser/parse '[x x])})}]
     (delta-step def-env
                 (parser/parse def-env '[y (test [t t])])))))
 => '(y (t t (t t))))

(example
 (stx/unparse-ln
  (first
   (let [def-env {'test (defenv/map->Definition
                          {:arity 2
                           :tag :definition
                           :params '[[x ✳] [y ✳]]
                           :parsed-term (parser/parse '[x [y x]])})}]
     (delta-step def-env
                 (parser/parse def-env '[y (test [t t] u)])))))
 => '(y (t t (u (t t)))))


;;{
;; ## Reduction of specials
;;}

(defn special-reduction [def-env ctx t]
  ;; (println "[special-reduction] t=" t)
  (if (not (stx/ref? t))
    (throw (ex-info "Cannot special-reduce: not a reference term." {:term t}))
    (let [[status sdef] (defenv/fetch-definition def-env (:name t))]
      (if (= status :ko)
        [t false] ;; No error?  or (throw (ex-info "No such definition" {:term t :def-name name}))
        ;;(if (> (count (:args t)) (:arity sdef))
          ;;(throw (ex-info "Too many arguments to instantiate special." {:term t :def-name name :nb-params (count (:arity sdef)) :nb-args (count (:args t))}))
          (if (special? sdef)
            ;;(if (< (count (:args t)) (:arity sdef))
            ;;(throw (ex-info "Not enough argument for special definition." { :term t :arity (:arity sdef)}))
            (do
              ;; (println "[special-reduction] sdef=" sdef)
              (let [term (apply (:special-fn sdef) def-env ctx (:args t))]
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
    ;; 1) try reduction in binding type
    (let [[ty red1?] (special-step def-env ctx (:type t))
          ;; 2) try reduction in body
          [body red2?] (special-step def-env ctx (:body t))]
      [((stx/binder-fn t) (:name t) ty body) (or red1? red2?)])
    ;; application
    (stx/app? t)
    (let [;; 1) try left reduction
          [left lred?] (special-step def-env ctx (:left t))
          ;; 2) try right reduction
          [right rred?] (special-step def-env ctx (:right t))]
      [(stx/mk-app left right) (or lred? rred?)])
    ;; reference
    (stx/ref? t)
    (let [[args red1?] (special-step-args def-env ctx (:args t))
          t' (if red1? (stx/mk-ref (:name t) args) t)
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
 (stx/unparse
  (normalize (parser/parse '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))))
 => '(λ [y ✳] y))

(defn beta-eq?
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
     (stx/alpha-eq? t1' t2'))))

(example
 (beta-eq? (parser/parse '(λ [z ✳] z))
           (parser/parse '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y])))
 => true)


