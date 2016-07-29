
# A Logician's Dream

Mathematical logic is concerned with the formalization of reasoning about mathematical content.

## On mathematical content

LaTTe supports four main forms of  *mathematical content*:

  - **definitions** of mathematical concepts,
  
  - statements of **axioms** asserting unprovable (or not knowingly provable, or too difficult
   to prove) logical properties of defined concepts.

  - statements of **theorems** asserting expected logical properties of defined concepts,
  
  - the most important **proofs** of these theorems: certificates that they are, indeed, true,
  

(LaTTe also supports the notion of **specials** that cannot really be assimilated to
mathematical content, but rather as a bridge between mathematics and informatics).

An example of a **definition** is the notion of a surjective function:

> A function F:T->U is **surjective** if forall y in U, exists x in T such that (F x) = y.

In LaTTe this is defined as [[latte.rel/surjective]], which we reproduce below :

```clojure
(definition surjective
  "A surjective function."
  [[T :type] [U :type] [F (==> T U)]]
  (forall [y U] (exist [x T] (equal U (F x) y))))
```

Apart from being more formal, the LaTTe definition appears as quite faithful to the
 common definition (and important difference is the use of types and not (directly) sets,
  which will be discussed below).
  
An example of an **axiom** (namely of Peano arithmetics) follows:

> The successor function on integers is bijective.

In LaTTe such an axiom can be stated as follows:

```clojure
(defaxiom succ-bijective
  "The successor function is bijective."
  []
  (rel/bijective int int succ))
```

(cf. [[latte.rel/bijective]])

Based on a set of basic axioms and defined concepts, the working mathematician's routine is to state
theorems and provide proofs of such theorems. This is also, of course, the routine of the LaTTe used.

Here is an example of a theorem:

> The successor function is surjective.

This is stated as follows in LaTTe:

```clojure
(defthm succ-surjective
  "The successor function is surjective."
  []
  (rel/surjective int int succ))
```

The proof for this theorem is of course trivial.

> We now by an axiom that the successor function is bijective, hence it
> is also surjective (and injective). Qed.

In LaTTe, this simple proof can also be expressed, e.g. as follows:

```clojure
(proof succ-surjective :term
  ((rel/bijective-is-surjective int int succ) succ-bijective))
```

This can be interpred as follows:

> The proof of the theorem [[latte.rel/bijective-is-surjective]] is a function
> that can take a proof that something is bijective, and deduce from this
> that this same something is also surjective. This proof is applied to
> the axiom `succ-bijective` to yield the expected result.

The last form of mathematical content available is a notion of a library,
 book or theory, allowing to regroup a set of definitions, axioms, theorems
  and proofs under a common name (e.g. *group theory*, *graph theory*, etc.).
Latte here only exploit the Clojure programming environment, where the primary
 feature is called a namespace (but there is also a powerful notion of
  deployable library based on the JVM ecosystem).

## Informal vs. formal reasoning

