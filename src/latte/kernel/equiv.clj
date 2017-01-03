(ns latte.kernel.equiv

  "A fast(er) equivalence algorithm."

  (:require [latte.kernel.syntax :as stx]
            [latte.kernel.norm :as norm]))


(defn mkfresh-id [vmap]
  (count vmap))

(declare beta-equiv-args)
(declare dig-equiv)

(defn beta-equiv
  ([def-env ctx t1 t2] (beta-equiv def-env ctx t1 t2 {} {}))
  ([def-env ctx t1 t2 vmap1 vmap2]

    (cond
      ;; both terms are references
      (and (stx/ref? t1)
           (stx/ref? t2))
      (let [[name1 & args1] t1
            [name2 & args2] t2]
        (if (and (= name1 name2)
                 (beta-equiv-args def-env ctx args1 args2 vmap1 vmap2))
          [:ok {}]
          (let [[t1' red1?] (norm/delta-reduction def-env t1)
                [t2' red2?] (norm/delta-reduction def-env t2)]
            (if (or red1? red2?)
              (recur def-env ctx t1' t2' vmap1 vmap2)
              [:ko {:msg "Mismatch references"
                    :term1 t1
                    :term2 t2}]))))

      ;; only the left term is a reference
      (stx/ref? t1)
      (let [[t1' red?] (norm/delta-reduction def-env t1)]
        (if red?
          (recur def-env ctx t1' t2 vmap1 vmap2)
          [:ko {:msg "Term1 not delta-reducible"
                :term1 t1
                :term2 t2}]))
      ;; only the right term is a reference
      (stx/ref? t2)
      (let [[t2' red?] (norm/delta-reduction def-env t2)]
        (if red?
          (recur def-env ctx t1 t2' vmap1 vmap2)
          [:ko {:msg "Term2 not delta-reducible"
                :term1 t1
                :term2 t2}]))
      ;; hitherto there is no reference, neither on the left nor on the right
      ;; now we handle the beta-redex

      ;; left term is a redex
      (norm/redex? t1)
      (recur def-env ctx (norm/beta-reduction t1) t2 vmap1 vmap2)

      ;; right term is a redex
      (norm/redex? t2)
      (recur def-env ctx t1 (norm/beta-reduction t2) vmap1 vmap2)

      ;; kind
      (and (stx/kind? t1)
           (stx/kind? t2))
      [:ok {}]

      ;; type
      (and (stx/type? t1)
           (stx/type? t2))
      [:ok {}]

      ;; variable
      (and (stx/variable? t1)
           (stx/variable? t2))

      (if (or (= (get vmap1 t1 ::left)
                 (get vmap2 t2 ::right))
              (= t1 t2))
        [:ok {}]
        [:ko {:msg "Mismatch variables"
              :term1 t1
              :term2 t2}])

      ;; lambda
      (and (stx/lambda? t1)
           (stx/lambda? t2))

      (let [[_ [v1 ty1] body1] t1
            [_ [v2 ty2] body2] t2]
        (let [[status info] (beta-equiv def-env ctx ty1 ty2 vmap1 vmap2)]
          (if (= status :ko)
            [status info]
            ;;  XXX: is this working?
            (let [id (mkfresh-id vmap1)]
              (recur def-env ctx body1 body2 (assoc vmap1 v1 id) (assoc vmap2 v2 id))))))

      ;; product
      (and (stx/prod? t1)
           (stx/prod? t2))

      (let [[_ [v1 ty1] body1] t1
            [_ [v2 ty2] body2] t2]
        (let [[status info] (beta-equiv def-env ctx ty1 ty2 vmap1 vmap2)]
          (if (= status :ko)
            [status info]
            ;;  XXX: is this working?
            (let [id (mkfresh-id vmap1)]
              (recur def-env ctx body1 body2 (assoc vmap1 v1 id) (assoc vmap2 v2 id))))))


      ;; application
      (and (stx/app? t1)
           (stx/app? t2))

      (let [[rator1 rand1] t1
            [rator2 rand2] t2]
        (let [[status info] (beta-equiv def-env ctx rator1 rator2 vmap1 vmap2)]
          (if (= status :ok)
            (let [[status info] (beta-equiv def-env ctx rand1 rand2 vmap1 vmap2)]
              (if (= status :ok)
                [status info]
                (dig-equiv def-env ctx t1 t2 vmap1 vmap2)))
            (dig-equiv def-env ctx t1 t2 vmap1 vmap2))))
      :else
      (dig-equiv def-env ctx t1 t2 vmap1 vmap2))))



(defn dig-equiv
  [def-env ctx t1 t2 vmap1 vmap2]
  (let [[t1' red1?] (norm/delta-step def-env t1)]
    (if red1?
      (beta-equiv def-env ctx t1' t2 vmap1 vmap2)
      (let [[t1' red1?] (norm/beta-step t1)]
        (if red1?
          (beta-equiv def-env ctx t1' t2 vmap1 vmap2)
          (let [[t2' red2?] (norm/delta-step def-env t2)]
            (if red2?
              (beta-equiv def-env ctx t1 t2' vmap1 vmap2)
              (let [[t2' red2?] (norm/beta-step t2)]
                (if red2?
                  (beta-equiv def-env ctx t1 t2' vmap1 vmap2)
                  [:ko {:msg "Mismatch terms"
                        :term1 t1
                        :term2 t2}])))))))))


(defn beta-equiv-args
  [def-env ctx args1 args2 vmap1 vmap2]
  (if (seq args1)
    (if (seq args2)
      (let [[status info] (beta-equiv def-env ctx (first args1) (first args2) vmap1 vmap2)]
        (if (= status :ko)
          [status info]
          (recur def-env ctx (rest args1) (rest args2) vmap1 vmap2)))
      ;; not enough args2
      [:ko {:msg "Mismatch arity"
            :args1 args1
            :args2 args2}])
    (if (seq args2)
      [:ko {:msg "Mismatch arity"
            :args1 args1
            :args2 args2}]
      [:ok {}])))


