(ns latte.core-init
  (:require-macros [latte.core :refer [defnotation]]))


(defnotation lambda
  "The `lambda` notation for abstractions.

The simplest form is `(lambda [x T] e)` with
as `bindings` the variable `x` of type `T`, and
`e` as the abstraction `body`.

The low-level equivalent is `(λ [x T] e)`.

The extended notation `(lambda [x y z T] e)` is
equivalent to `(lambda [x T] (lambda [y T] (lambda [z T] e)))`."
  [bindings body]
  [:ok (list 'λ bindings body)])

;TODO: viebel (alter-meta! #'latte.core$macros/lambda update-in [:style/indent] (fn [_] [1 :form :form]))

(defnotation forall
  "The `lambda` notation for product abstractions.

The expression `(forall [x T] U)` is the type of an
abstraction of the form `(lambda [x T] e)` with `e`
 of type `U` when `x` is of type `P`.

The low-level equivalent is `(Π [x T] U)`.

The extended notation `(forall [x y z T] U)` is
equivalent to `(forall [x T] (forall [y T] (forall [z T] U)))`."
  [bindings body]
  [:ok (list 'Π bindings body)])

;TODO: viebel (alter-meta! #'forall update-in [:style/indent] (fn [_] [1 :form :form]))

(defnotation ==>
  "The function type, or equivalently logical implication.

  `(==> A B)` is `(Π [x A] B)` where `x` does not occur free in `B`.

Implication is right arrociative:

'(==> A B C) ≡ `(==> A (==> B C))`."
  [& arguments]
  [:ok (list* '⟶ arguments)])
