(ns latte.core-test
  (:require [latte.core :as sut :refer [defthm]]
            [clojure.test :as t :refer [deftest is]]))

(defn mk-impl-refl! []
  (defthm impl-refl
    "Implication is reflexive."
    [[A :type]]
    (==> A A)))

(defn unmk-impl-refl! []
  (ns-unmap *ns* 'impl-refl))


(deftest simple-theorem-impl-refl
  (let [message (mk-impl-refl!)
        impl-refl-val (ns-resolve *ns* 'impl-refl)
        _ (unmk-impl-refl!)]
    (is (= message [:declared :theorem 'impl-refl]))))






