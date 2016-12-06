(ns latte.prop
  "Basic definitions and theorems for (intuitionistic) propositional logic.
  Most natural deduction rules are provided as theorems in this namespace."

  (:refer-clojure :exclude [and or not])

  (:require [latte.kernel.syntax :as stx]
            [latte.kernel.typing :as ty]
            [latte.kernel.norm :as norm]
            [latte.core :as latte :refer [definition term type-of defthm defspecial
                                          lambda forall ==>
                                          assume have qed proof try-proof]]))

(defthm impl-refl
  "Implication is reflexive."
  [[A :type]]
  (==> A A))

;; (proof impl-refl
;;        :term
;;        (lambda [x A] x))

(proof impl-refl :script
  (assume [x A]
    (have concl A :by x)
    (qed concl)))

(defthm impl-ignore
  "A variant of reflexivity."
  [[A :type] [B :type]]
  (==> A B A))

(proof impl-ignore
    :term (lambda [x A]
            (lambda [y B] x)))

(defthm impl-trans
  "Implication is transitive."
  [[A :type] [B :type] [C :type]]
  (==> (==> A B)
       (==> B C)
       (==> A C)))

(proof impl-trans
    :script
  (assume [H1 (==> A B)
           H2 (==> B C)
           x A]
    (have <a> B :by (H1 x))
    (have <b> C :by (H2 <a>))
    (qed <b>)))

(defn decompose-impl-type
  [def-env ctx t]
  (if (stx/prod? t)
    (let [[_ [_ A] B] t]
      ;; TODO: check that the product variable is not in use ?
      [:ok A B])
    (let [[t ok?] (latte.kernel.norm/delta-step def-env t)]
      (if ok?
        (recur def-env ctx t)
        (let [t (latte.kernel.norm/normalize def-env ctx t)]
          (if (stx/prod? t)
            (let [[_ [_ A] B] t]
              ;; TODO: check that the product variable is not in use ?
              [:ok A B])))))))

(defspecial impl-trans%
  "Transitivity of implication, a special version of [[impl-trans]]."
  [def-env ctx impl-term1 impl-term2]
  (let [[status ty1] (ty/type-of-term def-env ctx impl-term1)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/impl-trans%
                                           :term impl-term1
                                           :from ty1})))    
    (let [[status ty2] (ty/type-of-term def-env ctx impl-term2)]
      (when (= status :ko)
        (throw (ex-info "Cannot type term." {:special 'latte.prop/impl-trans%
                                             :term impl-term2
                                             :from ty2})))
      (let [[status A B] (decompose-impl-type def-env ctx ty1)]
        (when (= status :ko)
          (throw (ex-info "Not an `==>`-type." {:special 'latte.prop/impl-trans%
                                                :term impl-term1
                                                :type ty1})))
      (let [[status B' C] (decompose-impl-type def-env ctx ty2)]
        (when (= status :ko)
          (throw (ex-info "Not an `==>`-type." {:special 'latte.prop/impl-trans%
                                                :term impl-term2
                                                :type ty2})))
        
        (when-not (norm/beta-eq? def-env ctx B B')
          (throw (ex-info "Type in the middle mismatch" {:special 'latte.prop/impl-trans%
                                                         :left-rhs-type B
                                                         :right-lhs-type B'})))
        [[(list #'iff-trans A B C) impl-term1] impl-term2])))))

(definition absurd
  "Absurdity."
  []
  (forall [α :type] α))

(defthm ex-falso
  "Ex falso sequitur quodlibet
   (proof by contradiction, elimination for absurdity)."
  [[A :type]]
  (==> absurd A))

;; (proof ex-falso
;;        :term
;;        (lambda [f absurd] (f A)))

(proof ex-falso
    :script
  (assume [f absurd]
    (have a A :by (f A))
    (qed a)))

(definition not
  "Logical negation."
  [[A :type]]
  (==> A absurd))

(defthm absurd-intro
  "Introduction rule for absurdity."
  [[A :type]]
  (==> A (not A)
       absurd))

;; (proof absurd-intro
;;        :term
;;        (lambda [x A]
;;          (lambda [y (neg A)]
;;            (y x))))

(proof absurd-intro
    :script
  (assume [x A
           y (not A)]
    (have a absurd :by (y x))
    (qed a)))

(defthm impl-not-not
  "The if half of double negation.

This can be seen as an introduction rule for ¬¬ (not-not) propositions.
Note that double-negation is a law of classical (non-intuitionistic) logic."
  [[A :type]]
  (==> A (not (not A))))

;; (neg (neg A))
;; = (==> (neg A) absurd)
;; = (==> (==> A absurd) absurd) 

(proof impl-not-not
    :script
  (assume [x A
           H (not A)]
    (have a absurd :by (H x))
    (qed a)))

(definition truth
  "Logical truth."
  []
  (not absurd))

(defthm truth-is-true
  "The truth is true (really ?)."
  []
  truth)

(proof truth-is-true :script
  (have a truth :by (impl-refl absurd))
  (qed a))

(definition and
  "logical conjunction."
  [[A :type] [B :type]]
  (forall [C :type]
    (==> (==> A B C)
         C)))

(defthm and-intro
  "Introduction rule for logical conjunction."
  [[A :type] [B :type]]
  (==> A B
       (and A B)))

;; (proof land-intro
;;        :term
;;        (lambda [x A]
;;          (lambda [y B]
;;            (lambda [C :type]
;;              (lambda [z (==> A B C)]
;;                z x y)))))

(proof and-intro
    :script
  (assume [x A
           y B
           C :type
           z (==> A B C)]
    (have a (==> B C) :by (z x))
    (have b C :by ((a) y))
    (qed b)))

(defspecial and-intro%
  "A special introduction rule that takes a proof
`a` of type `A`, a proof `b` of type `B` and yields
a proof of type `(and A B)`.

This is a special version of [[and-intro]]."
  [def-env ctx a b]
  (let [[status-a ty-a] (ty/type-of-term def-env ctx a)
        [status-b ty-b] (ty/type-of-term def-env ctx b)]
    (cond
      (= status-a :ko)
      (throw (ex-info "Cannot type left-hand term."
                      {:special 'latte.prop/and-intro%
                       :term a
                       :from ty-a}))
      (= status-b :ko)
      (throw (ex-info "Cannot type right-hand term."
                      {:special 'latte.prop/and-intro%
                       :term b
                       :from ty-b}))
      :else
      [[(list #'and-intro ty-a ty-b) a] b])))

(defthm and-elim-left
  "Elimination rule for logical conjunction.
   This one only keeps the left-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       A))

(proof and-elim-left :script
  (assume [H1 (and A B)]
    (have a (==> (==> A B A) A) :by (H1 A))
    (have b (==> A B A) :by (impl-ignore A B))
    (have c A :by (a b))
    (qed c)))

(defn decompose-and-type [def-env ctx t]
  (if (clojure.core/and (seq? t) 
                        (= (count t) 3)
                        (= (first t) #'latte.prop/and))
    [:ok (second t) (nth t 2)]
    (let [[t ok?] (latte.kernel.norm/delta-step def-env t)]
      (if ok?
        (recur def-env ctx t)
        (let [t (latte.kernel.norm/normalize def-env ctx t)]
          (if-not (stx/prod? t)
            [:ko nil nil]
            (let [[_ [z _] body] t]
              (if-not (stx/prod? body)
                [:ko nil nil]
                (let [[_ [_ hyp] concl] body]
                  (if-not (stx/prod? hyp)
                    [:ko nil nil]
                    (let [[_ [_ a] nxt] hyp]
                      (if-not (stx/prod? nxt)
                        [:ko nil nil]
                        (let [[_ [_ b] end] nxt]
                          (if-not (= z concl end)
                            [:ko nil nil]
                            [:ok a b]))))))))))))))

(defspecial and-elim-left%
  "A special elimination rule that takes a proof
of type `(and A B)` and yields a proof of `A`.

This is a special version of [[and-elim-left]]."
  [def-env ctx and-term]
  (let [[status ty] (ty/type-of-term def-env ctx and-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/and-elim-left%
                                           :term and-term
                                           :from ty}))
      (do
        ;; (println "[and-elim-left%] ty=" ty)
        (let [[status A B] (decompose-and-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `and`-type." {:special 'latte.prop/and-elim-left%
                                                  :term and-term
                                                  :type ty}))
            [(list #'and-elim-left A B) and-term]))))))

(defthm and-elim-right
  "Elimination rule for logical conjunction.
   This one only keeps the right-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       B))

(proof and-elim-right
    :script
  (assume [H1 (and A B)]
    (have a (==> (==> A B B) B) :by (H1 B))
    (have b (==> A B B) :by (lambda [x A]
                              (lambda [y B]
                                y)))
    (have c B :by (a b))
    (qed c)))

(defspecial and-elim-right%
  "A special elimination rule that takes a proof
of type `(and A B)` and yields a proof of `B`.

This is a special version of [[and-elim-right]]."
  [def-env ctx and-term]
  (let [[status ty] (ty/type-of-term def-env ctx and-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/and-elim-right%
                                           :term and-term
                                           :from ty}))
      (do
        (let [[status A B] (decompose-and-type def-env ctx ty)]
          ;; (println "[and-elim-right%] A=" A "B=" B)
          (if (= status :ko)
            (throw (ex-info "Not an `and`-type." {:special 'latte.prop/and-elim-right%
                                                  :term and-term
                                                  :type ty}))
            [(list #'and-elim-right A B) and-term]))))))

(defthm and-sym
  "Symmetry of conjunction."
  [[A :type] [B :type]]
  (==> (and A B)
       (and B A)))

(proof and-sym :script
  (assume [H (and A B)]
    ;; (have a A :by ((and-elim-left A B) H))
    (have <a> A :by (and-elim-left% H))
    ;;(have b B :by ((and-elim-right A B) H))
    (have <b> B :by (and-elim-right% H))
    (have <c> (==> B A
                 (and B A)) :by (and-intro B A))
    (have <d> (and B A) :by (<c> <b> <a>))
    (qed <d>)))

(defspecial and-sym%
  "Symmetry of conjunction, a special version of [[and-sym]]."
  [def-env ctx and-term]
  (let [[status ty] (ty/type-of-term def-env ctx and-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/and-sym%
                                           :term and-term
                                           :from ty}))
      (do
        (let [[status A B] (decompose-and-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `and`-type." {:special 'latte.prop/and-sym%
                                                  :term and-term
                                                  :type ty}))
            [(list #'and-sym A B) and-term]))))))

(definition or
  "logical disjunction."
  [[A :type] [B :type]]
  (forall [C :type]
    (==> (==> A C)
         (==> B C)
         C)))

(defthm or-intro-left
  "Introduction rule for logical disjunction.
This is the introduction by the left operand."
  [[A :type] [B :type]]
  (==> A
       (or A B)))

(proof or-intro-left
    :script
  (assume [x A
           C :type
           H1 (==> A C)
           H2 (==> B C)]
    (have a C :by (H1 x))
    (qed a)))

(defspecial or-intro-left%
  "Left introduction for disjunction, a special version of [[or-intro-left]]."
  [def-env ctx left-type right-term]
  (when-not (ty/proper-type? def-env ctx left-type)
    (throw (ex-info "Not a type." {:special 'latte.prop/or-intro-left%
                                   :term left-type})))
  (let [[status right-type] (ty/type-of-term def-env ctx right-term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/or-intro-left%
                                           :term right-term
                                           :from right-type})))
    [(list #'or-intro-left left-type right-type) right-term]))

(defthm or-intro-right
  "Introduction rule for logical disjunction.
This is the introduction by the right operand."
  [[A :type] [B :type]]
  (==> B
       (or A B)))

(proof or-intro-right
    :script
  (assume [y B
           C :type
           H1 (==> A C)
           H2 (==> B C)]
    (have a C :by (H2 y))
    (qed a)))

(defspecial or-intro-right%
  "Right introduction for disjunction, a special version of [[or-intro-right]]."
  [def-env ctx left-term right-type]
  (when-not (ty/proper-type? def-env ctx right-type)
    (throw (ex-info "Not a type." {:special 'latte.prop/or-intro-right%
                                   :term right-type})))
  (let [[status left-type] (ty/type-of-term def-env ctx left-term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/or-intro-right%
                                           :term left-term
                                           :from left-type})))
    [(list #'or-intro-right left-type right-type) left-term]))

(defthm or-elim
  "Elimination rule for logical disjunction.

Remark: this rule,
reflecting the definition of [[or]], provides a
 constructive way to eliminate disjunctions. 
A simpler elimination process is offered if one
 of the two disjuncts does not hold: 
cf. [[or-not-elim-left]] and [[or-not-elim-right]]."
  [[A :type] [B :type]]
  (==> (or A B)
       (forall [C :type]
         (==> (==> A C)
              (==> B C)
              C))))

(proof or-elim
    :script
  (assume [H1 (forall [D :type] (==> (==> A D)
                                     (==> B D)
                                     D))
           C :type
           H2 (==> A C)
           H3 (==> B C)]
    (have a (==> (==> A C) (==> B C) C) :by (H1 C))
    (have b (==> (==> B C) C) :by (a H2))
    (have c C :by (b H3))
    (qed c)))


;; (or A B)
;; = (forall [C :type]
;;       (forall [_ (forall [_ A] C)]
;;          (forall [_ (forall [_ B C])]
;;               C)))

(defn decompose-or-type [def-env ctx t]
  (if (clojure.core/and (seq? t) 
                        (= (count t) 3)
                        (= (first t) #'latte.prop/or))
    [:ok (second t) (nth t 2)]
    (let [[t ok?] (latte.kernel.norm/delta-step def-env t)]
      (if ok?
        (recur def-env ctx t)
        (let [t (latte.kernel.norm/normalize def-env ctx t)]
          (if-not (stx/prod? t)
            [:ko nil nil]
            (let [[_ [C _] body] t]
              (if-not (stx/prod? body)
                [:ko nil nil]
                (let [[_ [_ AC] C'] body]
                  (if-not (and (= C' C) (stx/prod? AC))
                    [:ko nil nil]
                    (let [[_ [_ A] C'] AC]
                      (if-not (and (= C' C) (stx/prod? body))
                        [:ko nil nil]
                        (let [[_ [_ BC] C'] body]
                          (if-not (and (= C' C) (stx/prod? AC))
                            [:ko nil nil]
                            (let [[_ [_ B] C'] BC]
                              (if-not (= C' C)
                                [:ko nil nil]
                                [:ok A B]))))))))))))))))

(defspecial or-elim%
  "A special elimination rule that takes a proof
 `or-term` of type `(or A B)`, a proposition `prop`,
a proof `left-proof` of type `(==> A prop)`, 
a proof `right-proof` of type `(==> B prop)`, and thus
concludes that `prop` holds by `[[or-elim]]`.

This is (for now) the easiest rule to use for proof-by-cases."
  [def-env ctx or-term prop left-proof right-proof]
  (let [[status ty] (ty/type-of-term def-env ctx or-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/or-elim%
                                           :term or-term
                                           :from ty}))
      (do
        ;; (println "[and-elim-left%] ty=" ty)
        (let [[status A B] (decompose-or-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `or`-type." {:special 'latte.prop/or-elim%
                                                 :term or-term
                                                 :type ty}))
            [[[[(list #'or-elim A B) or-term] prop] left-proof] right-proof]))))))

(defthm or-not-elim-left
  "An elimination rule for disjunction, simpler than [[or-elim]].
This eliminates to the left operand."
  [[A :type] [B :type]]
  (==> (or A B) (not B)
       A))

(proof or-not-elim-left
    :script
  (assume [H1 (or A B)
           H2 (not B)]
    (have <a> (==> (==> A A) (==> B A) A) :by (H1 A))
    (have <b> (==> A A) :by (impl-refl A))
    (assume [x B]
      (have <c> absurd :by (H2 x))
      (have <d> A :by (<c> A)))
    (have <e> A :by (<a> <b> <d>))
    (qed <e>)))

(defthm or-not-elim-right
  "An elimination rule for disjunction, simpler than [[or-elim]].
This eliminates to the right operand."
  [[A :type] [B :type]]
  (==> (or A B) (not A)
       B))

(proof or-not-elim-right
    :script
  (assume [H1 (or A B)
           H2 (not A)]
    (have <a> (==> (==> A B) (==> B B) B) :by (H1 B))
    (have <b> (==> B B) :by (impl-refl B))
    (assume [x A]
      (have <c> absurd :by (H2 x))
      (have <d> B :by (<c> B)))
    (have <e> B :by (<a> <d> <b>))
    (qed <e>)))

(defthm or-sym
  "Symmetry of disjunction."
  [[A :type] [B :type]]
  (==> (or A B)
       (or B A)))

(proof or-sym :script
  (assume [H1 (or A B)
           D :type
           H2 (==> B D)
           H3 (==> A D)]
    (have a _ :by (H1 D))
    (have b D :by (a H3 H2))
    (qed b)))

(defspecial or-sym%
  "Symmetry of disjunction, a special version of [[or-sym]]."
  [def-env ctx or-term]
  (let [[status ty] (ty/type-of-term def-env ctx or-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/or-sym%
                                           :term or-term
                                           :from ty}))
      (do
        (let [[status A B] (decompose-or-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `or`-type." {:special 'latte.prop/or-sym%
                                                 :term or-term
                                                 :type ty}))
            [(list #'or-sym A B) or-term]))))))

(defthm or-not-impl-elim
  "An alternative elimination rule for disjunction."
  [[A :type] [B :type]]
  (==> (or A B)
       (==> (not A) B)))

(proof or-not-impl-elim :script
  (assume [H (or A B)
           Hn (not A)]
    (assume [x A]
      (have a absurd :by (Hn x))
      "Thanks to absurdity we can get anything we want."
      (have b B :by (a B)))
    (have c (==> B B) :by (impl-refl B))
    (have d (==> (==> A B)
                 (==> B B)
                 B) :by (H B))
    (have e B :by (d b c))
    (qed e)))

(definition <=>
  "Logical equivalence or 'if and only if'."
  [[A :type] [B :type]]
  (and (==> A B)
       (==> B A)))

(defthm iff-refl
  "Reflexivity of logical equivalence."
  [[A :type]]
  (<=> A A))

(proof iff-refl
    :script
  (have a (==> A A) :by (impl-refl A))
  (have b (==> (==> A A)
               (==> A A)
               (<=> A A)) :by
        (and-intro (==> A A) (==> A A)))
  (have c (<=> A A) :by (b a a))
  (qed c))

(defthm iff-intro
  "Introduction rule for logical equivalence."
  [[A :type] [B :type]]
  (==> (==> A B)
       (==> B A)
       (<=> A B)))

(proof iff-intro
    :script
  (assume [H1 (==> A B)
           H2 (==> B A)]
    (have a (==> (==> A B)
                 (==> B A)
                 (<=> A B)) :by (and-intro (==> A B) (==> B A)))
    (have b (<=> A B) :by (a H1 H2))
    (qed b)))

(defthm iff-elim-if
  "Elimination rule for logical equivalence.
   This one only keeps the if part of the equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (==> A B)))

(proof iff-elim-if
    :script
  (assume [H (<=> A B)]
    (have a (==> (<=> A B)
                 (==> A B))
          :by (and-elim-left (==> A B) (==> B A)))
    (have b (==> A B) :by (a H)))
  (qed b))

(defn decompose-iff-type
  [def-env ctx t]
  (let [[status L R] (decompose-and-type def-env ctx t)]
    (if (= status :ko)
      [:ko nil nil]
      (let [[status A B] (decompose-impl-type def-env ctx L)]
        (if (= status :ko)
          [:ko nil nil]
          [:ok A B])))))

(defspecial iff-elim-if%
  "Left (if) elimination for `<=>`, a special version of [[iff-elim-if]]."
  [def-env ctx iff-term]
  (let [[status ty] (ty/type-of-term def-env ctx iff-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/iff-elim-if%
                                           :term iff-term
                                           :from ty}))
      (do
        (let [[status A B] (decompose-iff-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `iff`-type." {:special 'latte.prop/iff-elim-if%
                                                  :term iff-term
                                                  :type ty}))
            [(list #'iff-elim-if A B) iff-term]))))))

(defthm iff-elim-only-if
  "Elimination rule for logical equivalence.
   This one only keeps the only-if part of the equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (==> B A)))

(proof iff-elim-only-if
    :script
  (assume [H (<=> A B)]
    (have a (==> (<=> A B)
                 (==> B A))
          :by (and-elim-right (==> A B) (==> B A)))
    (have b (==> B A) :by (a H))
    (qed b)))

(defspecial iff-elim-only-if%
  "Right (only if) elimination for `<=>`, a special version of [[iff-elim-only-if]]."
  [def-env ctx iff-term]
  (let [[status ty] (ty/type-of-term def-env ctx iff-term)]
    (if (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/iff-elim-only-if%
                                           :term iff-term
                                           :from ty}))
      (do
        (let [[status A B] (decompose-iff-type def-env ctx ty)]
          (if (= status :ko)
            (throw (ex-info "Not an `iff`-type." {:special 'latte.prop/iff-elim-only-if%
                                                  :term iff-term
                                                  :type ty}))
            [(list #'iff-elim-only-if A B) iff-term]))))))

(defthm iff-sym
  "Symmetry of logical equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (<=> B A)))

(proof iff-sym
    :script
  (assume [H (<=> A B)]
    (have a (==> B A) :by ((iff-elim-only-if A B) H))
    (have b (==> A B) :by ((iff-elim-if A B) H))
    (have c (==> (==> B A)
                 (==> A B)
                 (<=> B A)) :by (iff-intro B A))
    (have d (<=> B A) :by (c a b))
    (qed d)))

(defspecial iff-sym%
  "Symmetry of `<=>`, a special version of [[iff-sym]]."
  [def-env ctx iff-term]
  (let [[status ty] (ty/type-of-term def-env ctx iff-term)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/iff-sym%
                                           :term iff-term
                                           :from ty})))
    (let [[status A B] (decompose-iff-type def-env ctx ty)]
      (when (= status :ko)
        (throw (ex-info "Not an `iff`-type." {:special 'latte.prop/iff-sym%
                                              :term iff-term
                                              :type ty})))
      [(list #'iff-sym A B) iff-term])))

(defthm iff-trans
  "Transitivity of logical equivalence."
  [[A :type] [B :type] [C :type]]
  (==> (<=> A B)
       (<=> B C)
       (<=> A C)))

(proof iff-trans
    :script
  (assume [H1 (<=> A B)
           H2 (<=> B C)]
    (have a (==> A B) :by ((iff-elim-if A B) H1))
    (have b (==> B C) :by ((iff-elim-if B C) H2))
    (have c _ :by (impl-trans A B C))
    (have d (==> A C) :by (c a b))
    (have e (==> C B) :by ((iff-elim-only-if B C) H2))
    (have f (==> B A) :by ((iff-elim-only-if A B) H1))
    (have g _ :by (impl-trans C B A))
    (have h (==> C A) :by (g e f))
    (have i _ :by (iff-intro A C))
    (have k (<=> A C) :by (i d h))
    (qed k)))


(defspecial iff-trans%
  "Transitivity of `<=>`, a special version of [[iff-trans]]."
  [def-env ctx iff-term1 iff-term2]
  (let [[status ty1] (ty/type-of-term def-env ctx iff-term1)]
    (when (= status :ko)
      (throw (ex-info "Cannot type term." {:special 'latte.prop/iff-trans%
                                           :term iff-term1
                                           :from ty1})))
    (let [[status ty2] (ty/type-of-term def-env ctx iff-term2)]
      (when (= status :ko)
        (throw (ex-info "Cannot type term." {:special 'latte.prop/iff-trans%
                                             :term iff-term2
                                             :from ty2})))
      (let [[status A B] (decompose-iff-type def-env ctx ty1)]
        (when (= status :ko)
          (throw (ex-info "Not an `iff`-type." {:special 'latte.prop/iff-trans%
                                                :term iff-term1
                                                :type ty1})))
        (let [[status C D] (decompose-iff-type def-env ctx ty2)]
          (when (= status :ko)
            (throw (ex-info "Not an `iff`-type." {:special 'latte.prop/iff-trans%
                                                  :term iff-term2
                                                  :type ty2})))
          (cond
            (norm/beta-eq? def-env ctx B C)
            [[(list #'iff-trans A B D) iff-term1] iff-term2]
            ;; allow a symmetry
            (norm/beta-eq? def-env ctx B D)
            [[(list #'iff-trans A B C) iff-term1] iff-term2]
            :else
            (throw (ex-info "Type in the middle mismatch"
                            {:special 'latte.prop/iff-trans%
                             :left-lhs-type B
                             :right-lhs-type C
                             :right-rhs-type D}))))))))


