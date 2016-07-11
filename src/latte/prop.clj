(ns latte.prop
  "Basic definitions and theorems for (intuitionistic) propositional logic.
  Most natural deduction rules are provided as theorems in this namespace."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [defterm term type-of defthm
                                          lambda forall assume proof try-proof]])
  )


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
    :term (lambda [x A] (lambda [y B] x)))

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
    (have (a) B :by (H1 x))
    (have (b) C :by (H2 (a)))
    (have (c) (==> A C) :discharge [x (b)])
    (qed (c))))

(defterm absurd
  "Absurdity."
  []
  (forall [α *] α))

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
    (have (a) A :by (f A))
    (qed (a))))

(defterm not
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
    (have (a) absurd :by (y x))
    (qed (a))))

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
    (have (a) absurd :by (H x))
    (qed (a))))


(defterm truth
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

(defterm and
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
    (have (a) (==> B C) :by (z x))
    (have (b) C :by ((a) y))
    (have (c) (==> (==> A B C)
                   C) :discharge [z (b)])
    (have (d) (and A B) :discharge [C (c)])
    (qed (d))))

(defthm and-elim-left
  "Elimination rule for logical conjunction.
   This one only keeps the left-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       A))

(proof and-elim-left
    :script
  (assume [H1 (and A B)]
    (have (a) (==> (==> A B A) A) :by (H1 A))
    (have (b) (==> A B A) :by (impl-ignore A B))
    (have (c) A :by ((a) (b)))
    (qed (c))))

(defthm and-elim-right
  "Elimination rule for logical conjunction.
   This one only keeps the right-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       B))

(proof and-elim-right
    :script
  (assume [H1 (and A B)]
    (have (a) (==> (==> A B B) B) :by (H1 B))
    (have (b) (==> A B B) :by (lambda [x A] (lambda [y B] y)))
    (have (c) B :by ((a) (b)))
    (qed (c))))

;; (defterm and
;;   "logical conjunction."
;;   [[A :type] [B :type]]
;;   (forall [C :type]
;;     (==> (==> A B C)
;;       C)))

(defthm and-sym
  "Symmetry of conjunction."
  [[A :type] [B :type]]
  (==> (and A B)
       (and B A)))

(proof and-sym :script
  (assume [H (and A B)]
    (have (a) A :by ((and-elim-left A B) H))
    (have (b) B :by ((and-elim-right A B) H))
    (have (c) (==> B A
                   (and B A)) :by (and-intro B A))
    (have (d) (and B A) :by ((c) (b) (a)))
    (qed (d))))

(defterm or
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
    (have (a) C :by (H1 x))
    (have (b) (==> (==> B C) C) :discharge [H2 (a)])
    (have (c) (==> (==> A C)
                   (==> B C)
                   C) :discharge [H1 (b)])
    (have (d) (or A B) :discharge [C (c)])
    (qed (d))))

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
    (have (a) C :by (H2 y))
    (have (b) (==> (==> B C) C) :discharge [H2 (a)])
    (have (c) (==> (==> A C)
                   (==> B C)
                   C) :discharge [H1 (b)])
    (have (d) (or A B) :discharge [C (c)])
    (qed (d))))

(defthm or-elim
  "Elimination rule for logical disjunction.

Remark: this rule is not very useful since it only
reflects the definition of `or`. This is unlike for classical logic, 
which offers a much simpler elimination process.
"
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
    (have (a) (==> (==> A C) (==> B C) C) :by (H1 C))
    (have (b) (==> (==> B C) C) :by ((a) H2))
    (have (c) C :by ((b) H3))
    (qed (c))))

(defthm or-sym
  "Symmetry of disjunction.

Remark: the proof for this theorem illustrates the non-trivial
characteristic of or-elimination."
  [[A :type] [B :type]]
  (==> (or A B)
       (or B A)))


(proof or-sym :script
  (assume [H1 (or A B)
           D :type
           H2 (==> A D)
           H3 (==> B D)]
    (have (a) _ :by (H1 D))
    (have (b) D :by ((a) H2 H3))
    (have (c) (==> (==> A D) D) :discharge [H2 (b)])
    (have (d) (==> (==> B D)
                   (==> A D)
                   D) :discharge [H3 (c)])
    (have (e) (or B A) :discharge [D (d)])
    (qed (e))))

(defthm or-not-impl-elim
  "An alternative elimination rule for disjunction."
  [[A :type] [B :type]]
  (==> (or A B)
       (==> (not A) B)))


(proof or-not-impl-elim :script
  (assume [H (or A B)
           Hn (not A)
           x A]
    (have (a) absurd :by (Hn x))
    (have (b) B :by ((a) B))
    (have (c) (==> A B) :discharge [x (b)])
    (have (d) (==> B B) :by (impl-refl B))
    (have (e) (==> (==> A B)
                   (==> B B)
                   B) :by (H B))
    (have (f) B :by ((e) (c) (d)))
    (qed (f))))

(defterm <=>
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
  (have (a) (==> A A) :by (impl-refl A))
  (have (b) (==> (==> A A)
                 (==> A A)
                 (<=> A A)) :by
        (and-intro (==> A A) (==> A A)))
  (have (c) (<=> A A) :by ((b) (a) (a)))
  (qed (c)))

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
    (have (a) (==> (==> A B)
                   (==> B A)
                   (<=> A B)) :by (and-intro (==> A B) (==> B A)))
    (have (b) (<=> A B) :by ((a) H1 H2))
    (qed (b))))

(defthm iff-elim-if
  "Elimination rule for logical equivalence.
   This one only keeps the if part of the equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (==> A B)))

(proof iff-elim-if
    :script
  (assume [H (<=> A B)]
    (have (a) (==> (<=> A B)
                   (==> A B)) :by (and-elim-left (==> A B) (==> B A)))
    (have (b) (==> A B) :by ((a) H))
    (qed (b))))

(defthm iff-elim-only-if
  "Elimination rule for logical equivalence.
   This one only keeps the only-if part of the equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (==> B A)))

(proof iff-elim-only-if
    :script
  (assume [H (<=> A B)]
    (have (a) (==> (<=> A B)
                   (==> B A)) :by (and-elim-right (==> A B) (==> B A)))
    (have (b) (==> B A) :by ((a) H))
    (qed (b))))

(defthm iff-sym
  "Symmetry of logical equivalence."
  [[A :type] [B :type]]
  (==> (<=> A B)
       (<=> B A)))

(proof iff-sym
    :script
  (assume [H (<=> A B)]
    (have (a) (==> B A) :by ((iff-elim-only-if A B) H))
    (have (b) (==> A B) :by ((iff-elim-if A B) H))
    (have (c) (==> (==> B A)
                   (==> A B)
                   (<=> B A)) :by (iff-intro B A))
    (have (d) (<=> B A) :by ((c) (a) (b)))
    (qed (d))))

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
    (have (a) (==> A B) :by ((iff-elim-if A B) H1))
    (have (b) (==> B C) :by ((iff-elim-if B C) H2))
    (have (c) _ :by (impl-trans A B C))
    (have (d) (==> A C) :by ((c) (a) (b)))
    (have (e) (==> C B) :by ((iff-elim-only-if B C) H2))
    (have (f) (==> B A) :by ((iff-elim-only-if A B) H1))
    (have (g) _ :by (impl-trans C B A))
    (have (h) (==> C A) :by ((g) (e) (f)))
    (have (i) _ :by (iff-intro A C))
    (have (k) (<=> A C) :by ((i) (d) (h)))
    (qed (k))))
