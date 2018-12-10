(ns latte.core-test
  (:require [latte.core :as sut :refer [definition defthm deflemma defaxiom]]
            [latte-kernel.defenv :as defenv]
            [clojure.test :as t :refer [deftest testing is]]))

;;{
;; Testing definitions
;;}

(definition disjunction
  "logical disjunction."
  [[A :type] [B :type]]
  (forall [C :type]
          (==> (==> A C)
               (==> B C)
               C)))

(deftest simple-definition
  (testing "disjunction"
    (is (defenv/definition? disjunction))))

;;{
;; Testing theorems
;;}


(defthm impl-refl
  "Implication is reflexive."
  [[A :type]]
  (==> A A))

(deftest simple-theorem
  (testing "implication is reflexive"
      (is (defenv/theorem? impl-refl))
      (is (= (:name impl-refl) 'impl-refl))
      (is (= (:params impl-refl) '[[A ✳]]))
      (is (= (:arity impl-refl) 1))
      (is (= (:type impl-refl) '(Π [⇧ A] A)))
      (is (nil? (:proof impl-refl)))
      ;; metadata
      (is (string? (:doc (meta #'impl-refl))))
      (is (= (:arglists (meta #'impl-refl)) '[[[A :type]]]))
      (is (not (:private (meta #'impl-refl))))))

;;{
;; Testing lemmas
;;}

(deflemma impl-refl-lemma
  "Implication is reflexive, as a lemma."
  [[A :type]]
  (==> A A))

(deftest simple-lemma
  (testing "implication is reflexive, as a lemma"
    (is (defenv/theorem? impl-refl-lemma))
    (is (= (:name impl-refl-lemma) 'impl-refl-lemma))
    (is (= (:params impl-refl-lemma) '[[A ✳]]))
    (is (= (:arity impl-refl-lemma) 1))
    (is (= (:type impl-refl-lemma) '(Π [⇧ A] A)))
    (is (nil? (:proof impl-refl-lemma)))
    ;; metadata
    (is (string? (:doc (meta #'impl-refl-lemma))))
    (is (= (:arglists (meta #'impl-refl-lemma)) '[[[A :type]]]))
    (is (:private (meta #'impl-refl-lemma)))))

;;{
;; Testing axioms
;;}

(defaxiom dummy-ax
  "A dummy axiom (could be a theorem)"
  [[A :type]]
  (disjunction A A))

(deftest simple-axiom
  (testing "a dummy axiom"
    (is (defenv/axiom? dummy-ax))))





