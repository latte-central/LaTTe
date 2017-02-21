(ns latte.equal
  "The formal definition of equality, and its basic properties."

  (:refer-clojure :exclude [and or not])

  (:require
   [latte.kernel.syntax :as stx]
   [latte.kernel.norm :as norm]
   [latte.kernel.typing :as ty]
   [latte.core :as latte :refer [definition defthm defspecial
                                          forall lambda ==>
                                          assume have proof]]
   [latte.prop :as p :refer [<=> and or not]]))

(definition equal
  "The intuitionistic, second-order definition of equality.
This corresponds to Leibniz's *indiscernibility of identicals*."
  [[T :type] [x T] [y T]]
  (forall [P (==> T :type)]
    (<=> (P x) (P y))))

(defn decompose-equal-type [def-env ctx t]
  (if (clojure.core/and (seq t)
                        (= (count t) 4)
                        (= (first t) #'latte.equal/equal))
    [:ok (second t) (nth t 2) (nth t 3)]
    (let [[t ok?] (norm/delta-step def-env t)]
      ;; (println "[decompose-equal-type] delta-term=" t " (reduced ? " ok? ")")
      (if ok?
        (recur def-env ctx t)
        (let [[t ok?] (norm/beta-step t)]
          (if ok?
            (recur def-env ctx t)
            ;; XXX: cannot decompose further because
            ;; we cannot retrieve the x and y of the
            ;; definition ... needs a form of unification.
            [:ko nil nil nil]))))))

(defthm eq-refl
  "The reflexivity property of equality."
  [[T :type] [x T]]
  (equal T x x))

(proof eq-refl :script
  (assume [P (==> T :type)]
    (have a (<=> (P x) (P x)) :by (p/iff-refl (P x)))
    (qed a)))

(defthm eq-sym
  "The symmetry property of equality."
  [[T :type] [x T] [y T]]
  (==> (equal T x y)
       (equal T y x)))

(proof eq-sym :script
  (assume [Heq (equal T x y)
           P (==> T :type)]
    (have a (<=> (P x) (P y)) :by (Heq P))
    (have b (<=> (P y) (P x)) :by ((p/iff-sym (P x) (P y)) a))
    (qed b)))

(defspecial eq-sym%
  "Symmetry of equality, a special version of [[eq-sym]]."
  [def-env ctx eq-term]
  (let [[status ty] (ty/type-of-term def-env ctx eq-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-sym%
                                           :term eq-term
                                           :from ty}))
      (do
        (let [[status T x y] (decompose-equal-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-sym%
                                                             :term eq-term
                                                             :type ty}))
            [(list #'eq-sym T x y) eq-term]))))))

(defthm eq-trans
  "The transitivity property of equality."
  [[T :type] [x T] [y T] [z T]]
  (==> (equal T x y)
       (equal T y z)
       (equal T x z)))

(proof eq-trans :script
  (assume [H1 (equal T x y)
           H2 (equal T y z)
           P (==> T :type)]
    (have a (<=> (P x) (P y)) :by (H1 P))
    (have b (<=> (P y) (P z)) :by (H2 P))
    (have c (<=> (P x) (P z))
          :by ((p/iff-trans (P x) (P y) (P z)) a b))
    (qed c)))


(defspecial eq-trans%
  "Transitivity of `equal`, a special version of [[eq-trans]]."
  [def-env ctx eq-term1 eq-term2]
  (let [[status ty1] (ty/type-of-term def-env ctx eq-term1)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-trans%
                                           :term eq-term1
                                           :from ty1})))
    (let [[status ty2] (ty/type-of-term def-env ctx eq-term2)]
      (when (= status :ko)
        (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-trans%
                                             :term eq-term2
                                             :from ty2})))
      (let [[status T1 x1 y1] (decompose-equal-type def-env ctx ty1)]
        (when (= status :ko)
          (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-trans%
                                                           :term eq-term1
                                                           :type ty1})))
        (let [[status T2 x2 y2] (decompose-equal-type def-env ctx ty2)]
          (when (= status :ko)
            (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-trans%
                                                             :term eq-term2
                                                             :type ty2})))
          ;; XXX: these are redundant and probably take time ...
          #_(when-not (norm/beta-eq? def-env ctx T1 T2)
            (throw (ex-info "Equal type mismatch"
                            {:special 'latte.prop/eq-trans%
                             :left-type T1
                             :right-type T2})))
          #_(when-not (norm/beta-eq? def-env ctx y1 x2)
            (throw (ex-info "Term in the middle mismatch"
                            {:special 'latte.prop/eq-trans%
                             :left-rhs-term y1
                             :right-lhs-term x2})))
          [[(list #'eq-trans T1 x1 y1 y2) eq-term1] eq-term2])))))

(defspecial eq-trans*
  "Transitivity of `equal`, a n-ary version of [[eq-trans%]].
The parameter `eq-terms` is a vector of at least two equalities.

For example:

```
(eq-trans* eq1 eq2)
==> (eq-trans% eq1 eq2)

(eq-trans* eq1 eq2 eq3)
==> (eq-trans% (eq-trans% eq1 eq2) eq3)

(eq-trans* eq1 eq2 eq3 eq4)
==> (eq-trans% (eq-trans% (eq-trans% eq1 eq2) eq3) eq4)
````
etc.
`"
  [def-env ctx & eq-terms]
  ;; (println "[eq-trans*] eq-terms=" eq-terms)
  ;; (when-not (and (seq eq-terms) (>= (count eq-terms) 2))
  ;;   (println "  ==> here 1")
  ;;   (throw (ex-info "There must be at least two arguments."
  ;;                   {:special 'latte.prop/eq-trans*
  ;;                    :arg eq-terms})))
  (let [[status ty1] (ty/type-of-term def-env ctx (first eq-terms))]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-trans*
                                           :term (first eq-terms)
                                           :from ty1})))
    (let [[status T x1 y1] (decompose-equal-type def-env ctx ty1)]
      (when (= status :ko)
        (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-trans*
                                                         :term (first eq-terms)
                                                         :type ty1})))
      (loop [eq-terms' (rest eq-terms), x1 x1, y1 y1, ret (first eq-terms)]
        (if (seq eq-terms')
          (let [[status ty2] (ty/type-of-term def-env ctx (first eq-terms'))]
            (when (= status :ko)
              (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-trans*
                                                   :term (first eq-terms')
                                                   :from ty2})))
            (let [[status _ x2 y2] (decompose-equal-type def-env ctx ty2)]
              (when (= status :ko)
                (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-trans*
                                                                 :term (first eq-terms')
                                                                 :type ty2})))
              (recur (rest eq-terms') x1 y2
                     [[(list #'eq-trans T x1 y1 y2) ret] (first eq-terms')])))
          ;; we're done
          (do
            ;; (println "  ==> ret=" ret)
            ret))))))

;; (defthm test-eq-trans
;;   [[T :type] [a T] [b T] [c T] [d T]]
;;   (==> (equal T a b)
;;        (equal T b c)
;;        (equal T c d)
;;        (equal T a d)))

;; (proof test-eq-trans
;;     :script
;;   (assume [H1 (equal T a b)
;;            H2 (equal T b c)
;;            H3 (equal T c d)]
;;      (have <a> (equal T a d)
;;            :by (eq-trans* H1 H2 H3))
;;     ;; (have <a> (equal T a c)
;;     ;;       :by (((eq-trans T a b c) H1) H2))
;;     ;; (have <b> (equal T a d)
;;     ;;       :by (((eq-trans T a c d) <a>) H3))
;;     (qed <a>)))

(defthm eq-subst
  "Substitutivity property of equality."
  [[T :type] [P (==> T :type)] [x T] [y T]]
  (==> (equal T x y)
       (P x)
       (P y)))

(proof eq-subst :script
  (assume [H1 (equal T x y)
           H2 (P x)]
    (have a (<=> (P x) (P y)) :by (H1 P))
    (have b (P y) :by ((p/iff-elim-if (P x) (P y)) a H2))
    (qed b)))

(defspecial eq-subst%
  "Substitutivity of `equal`, a special version of [[eq-subst]]."
  [def-env ctx P eq-term Px]
  (let [[status eq-ty] (ty/type-of-term def-env ctx eq-term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-subst%
                                           :term eq-term
                                           :from eq-ty})))
    (let [[status T x y] (decompose-equal-type def-env ctx eq-ty)]
      (when (= status :ko)
        (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-subst%
                                                         :term eq-term
                                                         :type eq-ty})))
      [[(list #'eq-subst T P x y) eq-term] Px])))

(defthm eq-cong
  "Congruence property of equality."
  [[T :type] [U :type] [f (==> T U)] [x T] [y T]]
  (==> (equal T x y)
       (equal U (f x) (f y))))

(proof eq-cong :script
  (assume [H1 (equal T x y)
           Q (==> U :type)]
    (assume [H2 (Q (f x))]
      (have a1 _ :by (eq-subst T (lambda [z T] (Q (f z))) x y))
      (have a (Q (f y)) :by (a1 H1 H2)))
    (have b (equal T y x) :by ((eq-sym T x y) H1))
    (assume [H3 (Q (f y))]
      (have c1 _ :by (eq-subst T (lambda [z T] (Q (f z))) y x))
      (have c (Q (f x)) :by (c1 b H3)))
    (have d (<=> (Q (f x)) (Q (f y))) :by ((p/iff-intro (Q (f x)) (Q (f y))) a c))
    (qed d)))

(defspecial eq-cong%
  "Congruence of `equal`, a special version of [[eq-cong]]."
  [def-env ctx f eq-term]
  (let [[status eq-ty] (ty/type-of-term def-env ctx eq-term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-cong%
                                           :term eq-term
                                           :from eq-ty})))
    (let [[status T x y] (decompose-equal-type def-env ctx eq-ty)]
      (when (= status :ko)
        (throw (ex-info "Cannot infer an `equal`-type." {:special 'latte.prop/eq-cong%
                                                         :term eq-term
                                                         :type eq-ty})))
      (let [[status f-ty] (ty/type-of-term def-env ctx f)]
        (when (= status :ko)
          (throw (ex-info "Cannot type term." {:special 'latte.prop/eq-cong%
                                               :term f
                                               :from f-ty})))
        (let [[status T' U] (p/decompose-impl-type def-env ctx f-ty)]
          (when (= status :ko)
            (throw (ex-info "Cannot infer an `==>`-type." {:special 'latte.prop/eq-cong%
                                                           :term f
                                                           :type f-ty})))
          [(list #'eq-cong T U f x y) eq-term])))))

(defthm eq-impl
  [[T :type] [P (==> T :type)] [x T] [y T]]
  (==> (equal T x y)
       (P x)
       (P y)))

(proof eq-impl
    :script
  (assume [H1 (equal T x y)
           H2 (P x)]
    (have <a> (<=> (P x) (P y))
          :by (H1 P))
    (have <b> (==> (P x) (P y))
          :by (p/and-elim-left% <a>))
    (have <c> (P y) :by (<b> H2))
    (qed <c>)))

(defthm eq-impl-sym
  [[T :type] [P (==> T :type)] [x T] [y T]]
  (==> (equal T x y)
       (P y)
       (P x)))

(proof eq-impl-sym
    :script
  (assume [H1 (equal T x y)
           H2 (P y)]
    (have <a> (equal T y x) :by (eq-sym% H1))
    (have <b> (P x) :by ((eq-impl T P y x) <a> H2))
    (qed <b>)))


