
# Lambda the ultimate

> (this document is copyright © 2016 Frédéric Peschanski under the Creative commons CC-BY-SA 4.0)

Much ink (and bits) have been spilled explaining (and explaining again) the
lambda-calculus. And this is what we shall do again here, albeit with quite
 a focused approach of comparing the lambda-calculus provided by the
  host language Clojure, to the one implemented by the kernel of LaTTe.

## Lambda for computing

Most modern programming languages support a form of functional programming
 in which functions are made first-class. Clojure, being a functional-first
  programming language, is of course a typical example. The *lambda* of
   Clojure is named `fn`. A primary use of `fn` is to create (in general short)
    anonymous functions. Let's take one of the simplest example: the identity function.

```clojure
(fn [x] x)
```

In the lambda terminology, this is called an **abstraction**. 
We say in `(fn [x] e)` that `x` is the *binding variable* and `e` (an arbitrary expression) is the *body* of
 the abstraction. All the *free ocurrences* of `x` in `e` become *bound* by the abstraction.

To see that the abstraction above represents the identity function, we can apply it to some value:

```clojure
((fn [x] x) 42)
;=> 42
```

We just encountered two other major ingredients of the lambda-calculus:

  - an **application** `(f e)` of a function `f` to lambda-term `e`

  - a **primitive value** (sometimes also called a constant) `42`

Let's take a slightly more complex example: the *church* encoding of
pairs in the lambda-calculus (here the one embedded in Clojure).

```clojure
(def pair (fn [x] (fn [y] (fn [z] ((z x) y)))))
(def fst (fn [p] (p (fn [x] (fn [y] x)))))
(def snd (fn [p] (p (fn [x] (fn [y] y)))))
```

Here are a few example:

```clojure
(def p1 ((pair "hello") 42))
(fst p1)
;=> "hello"
(snd p1)
;=> 42
```

Note that in Clojure we could define `pair` more conveniently as `(fn [x y] (fn [z] ((z x) y)))`
 such that the construction of a pair would be simpler, e.g. `(pair "hello" 42)`. However,
  it is simpler, at least conceptually, to only consider single-argument functions.

The Church thesis is that everything (at least numerically) computable can be expressed with similar
encodings in such a "simple" lambda-calculus (or equivalently by Turing machines). 
While most introductions provide long lists
 of encodings of things such as booleans, numbers, arithmetic operations, (etc.), we
  will *not*. The thing is, such encodings are in general not practical, and most often yield very slow
   computations.

Before dwelving into the main subject, reasoning with a lambda-calculus, we have to introduce (or remind of) two
important features: *alpha-conversion* and *beta-reduction*.

### Alpha-conversion
   
First, the syntax of the lambda-calculus relies on a (in fact) non-trivial notion
of equality named *alpha-equivalence*. Under some "non-conflicting" conditions (this is the non-trivial part),
 renaming a bound variable should not change the syntactic nature of a lambda-term.
 
 For example, both the following terms:
 
```clojure
(fn [x] x)
(fn [y] y)
```
 
represent the identity function. We say the the two terms are **alpha-convertible**.
 
However, if we consider the pairing function :
 
```clojure
(fn [x] (fn [y] (fn [z] ((z x) y))))
```
 
Then the following is *not* a correct alpha-conversion:
 
```clojure
(fn [x] (fn [z] (fn [z] ((z x) z))))
```
 
An easy counter-example follows:
 
```clojure
(def pair1 (fn [x] (fn [y] (fn [z] ((z x) y)))))
(def pair2 (fn [x] (fn [z] (fn [z] ((z x) z)))))
 
(snd ((pair1 "hello") 42))
;=> 42

(snd ((pair2 "hello") 42))
;=> #object[user$snd$fn__9927 0x24ee5473 "user$snd$fn__9927@24ee5473"]
```

The problem is that we renamed the bound variable `y` into `z` but `z` is
 already in use. However, the following works:

```clojure
(def pair1 (fn [x] (fn [y] (fn [z] ((z x) y)))))
(def pair2 (fn [x] (fn [w] (fn [z] ((z x) w)))))
 
(snd ((pair1 "hello") 42))
;=> 42

(snd ((pair2 "hello") 42))
;=> 42
```

The variable name `w` that was chosen is said *fresh*, and in this
case the renaming is "safe": the two-terms `pair1` and `pair2` are alpha-convertible.

In the practice of programming, we all now the importance of choosing good names for
function parameters. This degree of freedom is thanks to alpha-conversion.

### Beta-reduction

An important question is: what is the semantics of the lambda-calculus?
The theoretical beauty of the calculus is that it mostly relies on a single 
(at least apparently) simple rewrite rule: *beta-reduction*.

Let's consider again the identity function, called on an argument:

```clojure
((fn [x] x) 42)
```

While for practical reasons (especially efficiency) things are much more complex, the
computation triggered here can be summarized by the following rewrite:

```clojure
((fn [x] x) 42) --> 42
```

What happened is that the body of the function, the occurrence `x` was replaced by
the value `42`. This was a beta-reduction.
Let's take the pairing function for a more interesting example:

```clojure
;; ((pair "hello") 42) 
(((fn [x] (fn [y] (fn [z] ((z x) y))))
 "hello") 42)
--> ((fn [y] (fn [z] ((z 42) y)) "hello"))
--> (fn [z] ((z 42) "hello"))
```

Already two beta-reductions were performed, let's see what happen when
we take the second element of the pair.

```clojure
;; (snd ((pair "hello") 42))
((fn [p] (p (fn [x] (fn [y] y))))
 (fn [z] ((z 42) "hello")))
--> ((fn [z] ((z 42) "hello")) ;p
     (fn [x] (fn [y] y)))
--> (((fn [x] (fn [y] y)) 42) "hello")
--> ((fn [y] y) 42)
--> 42
```

Note that after 3 beta-reductions we found back our identity function.

In all the situations above, the beta-reduction was trigerred in the
context of a sub-expression of the form

`((fn [x] a) b)` where `a` and `b` are arbitrary expressions.
Such a sub-expression is called a reducible expression or *redex*.

The beta reduction says that such a redex can be rewritten as expression 
`a` in which all the (free) occurrences of `x` are replaced by `b`.

This looks like a simple rule but it is not. First, we should remember
that modifying a term such as `a` above should be done with great care
 in order to avoid name clashes. But most importantly if the easy part
  is to beta-reduce a redex, the main problem is to find one! For this
  we need a *strategy* to find a redex to reduce.
In terms of programming, the three most famous strategies are *call-by-value* (the one implemented by
  Clojure), *call-by-name* (that you can find as an option in e.g. Scala) and *call-by-need* (the one implemented in Haskell). We will not explain these (there are far better sources), but
 we have to remember two things:

  - beta-reduction is at the heart of the lambda-calculus semantics

  - a strategy to find the first redex to reduce must be established

And we have now everything at hand to explain the lambda-calculus
 driving LaTTe.

## Lambda for reasoning

The lambda-calculus was for a long time considered as a computational
artefact. But Church already felt the interest of the calculus, in its
 explicitely typed variant, from a logical point of view. This was later
  more deeply investigated by mathematicians, among them Curry, and
   then Howard (and many others, of course)... But wait, *Curry* ... *Howard* ...
    that sounds familiar. What we will investigate now is a deep connection
	 between calculating using the lambda-calculus, as we did in the previous
	  section, and reasoning ... also using the lambda-calculus. This
	   is the famous *Curry-Howard correspondance*.

### To type or not to type, that is (not) the question

The question *Why types?* is one of the great debates about programming. Clojure
 programmers obviously made a choice of relying on types at runtime (a.k.a. dynamic
  typing) instead of at compile-time (a.k.a. static typing). As a consequence, the
  lambda-calculus embedded in Clojure is itself of an *untyped* nature.

The expression `(fn [x] x)` does not contains any explicit (nor implicit) type information.
 Moreover, the Clojure compiler does not perform any type-checking when encoutering such an expression.

From a logical perspective, the question *Why types?* is also a debate
 but as far as the lambda-calculus is concerned, the question is more
 of the kind: *What kind of types?*.

There are two "schools" about this:

 - the *typing à la Curry* school

 - the *typing à la Church* school

In the Curry school, the idea is to consider the untyped terms, and try *a posteriori*
 to classify them according to their type. There is the underlying idea of *type reconstruction*
  behind Curry typing. Curry-typing is a very important principle in statically-typed functional
   programming languages. For example, if we write the identity function in Ocaml, we get:

```ocaml
 fun x -> x ;;
- : 'a -> 'a = <fun>
```

This is equivalent to say, for any type `'a`, then `fun x -> x`  (the Ocaml version of `(fn [x] x)`)
returns a value of the same type `'a`. Here, the `'a` is a *type variable*, a placeholder for a "real"
 type, e.g. `bool`, `int`, etc.  Curry typing is sometimes called *implicit typing*.

In the Church school, on the contrary, types must be explicit. Because it uses a very expressive
 lambda-calculus for which type reconstruction is not decidable,  LaTTe implements an explicitely typed lambda-calculus. 
 
 Suppose we have a type `A`, then the
 identity function for type `A` can be written in LaTTe as follows:

```clojure
(lambda [x A] x)
```

The `lambda` keyword is of course the `fn` of LaTTe. The variable `x` is explicited
 of having type `A`.

The type of the previous expression can be written in LaTTe: `(==> A A)` it is a function
 that takes an `A` and yields an `A`.

We have defined an identity function that is *specific* to a type `A` that has not
been specified. In clojure the function `(fn [x] x)` is very generic, it is an identity
functions for anything

```clojure
((fn [x] x) true) -> true ;; identity for `booleans`
((fn [x] x) 42) -> 42     ;; identity for `integers`
... etc ...
```

Is it possible to define such a generic function in LaTTe? The answer is of course yes,
 and this can be written as follows:

```clojure
(lambda [A :type]
  (lambda [x A] x))
```

The generic identity function first has a parameter `A` that is an arbitrary type, and it yields
 the identity function on `A`. We give to `A` the type `:type` to say that it *is* an arbitrary type.
  The constant `:type` is the *type of types*.

We can now apply the generic identity in an explicitely-typed context:

```clojure
(((lambda [A :type] (lambda [x A] x)) boolean) true)
--> ((lambda [x boolean] x) true)
--> true
```
or:

```clojure
(((lambda [A :type] (lambda [x A] x)) int) 42)
--> ((lambda [x int] x) 42)
--> 42
```

This is clearly a little bit more verbose, so
we need a more serious argument in favor of typing. For we should answer the question:

> What is the type of `(lambda [A :type] (lambda [x A] x))`?

An adequate answer is obtained thanks to a lambda-calculus named *system F* (or *λ2*, or the polymorphic
  lambda-calculus), and in LaTTe it is as follows:

```
(forall [A :type]
  (==> A A))
```

Note that it is in fact the same type that is reconstructed by Ocaml for the expression `fun x -> x`.

As a computational statement, the expression above reads:

> for an arbitrary type `A`, get a function that takes an `A` and yields an `A`.

As a logical statement, the alternative but equivalement reading is:

> for an arbitrary proposition `A`, it is true that `A` implies `A`.

But wait, this is a simple although fundamental property of propositional logic:
 *reflexivity of implication*.

Let's take a second example, slightly more complex.

Suppose we have a value `v` of type `A` and a function `f` of type `(==> A B)`.
The question is now:

> How to obtain a value of type `B`?

From a computational point of view, the answer is obvious: let's apply `f` to `v`,
 and of course `(f v)` is of type `B`.

Now let's translate this into logical statements... this gives:

 - suppose we have two propositions `A` and `B`

 - moreover we have a proof of `A` named `v`, and a proof of `(==> A B)` named `f`

 - a proof of `B` is `(f v)`.

What we just did is a *demonstration* that probably the most important rule of
logical deduction - the infamous *modus ponens* - is a natural interpretation of
 applying a function to a value in a (typed) lambda-calculus.

Amusingly, such a "proof" is already present in e.g. Ocaml:

```ocaml
(fun v -> (fun f -> f v))
- : 'a -> ('a -> 'b) -> 'b = <fun>
```

For the trained mind, this reads: "from a value of type `'a` and a function of type `'a -> 'b' 
get a value of type `b`. The function works also in Clojure of course:

```clojure
(((fn [v] (fn [f] (f v))) 42) even?)
;=> true
```

The function `even?` is (at least philosophically) of type `(==> int boolean)`, and
`42` is of type `int` hence we obtain a `boolean`.

In LaTTe, we can make all this quite explicit:

```clojure
(lambda [A :type]
  (lambda [B :type]
    (lambda [v A]
      (lambda [f (==> A B)]
        (f v)))))
```

The type of the expression above is as follows:

```clojure
(forall [A :type]
  (forall [B :type]
    (forall [v A]
       (forall [f (==> A B)]
          B))))
```

This is quite verbose so let's try to simplify this. We remark that in the type, there is
no occurrence of the variables `v` and `F` and we have the following law:

If `x` is a variable, `T` is a type and `U` is type in which there is no free occurrence of `x`, then:

```clojure
(forall  [x T] U) ≝ (==> T U)
```

(so implication is a special case of universal quantification)

Hence the type of our *modus ponens* example becomes:

```clojure
(forall [A :type]
  (forall [B :type]
    (==> A
         (==> (==> A B)
              B))))
```

that can be further simplified (using a simple *n-ary* version of implication) as follows:

```clojure
(forall [A :type]
  (forall [B :type]
    (==> A
         (==> A B)
         B)))
```

And the logical reading of this type is eloquent:

> - suppose `A` and `B` two arbitrary propositions
> - if we know that `A` is true
> - and moreover we know that `A` implies `B`
> - then `B` is true.

Logicians like to write this as an *inference rule*, as follows:

```
  A     A ==> B
==================
       B
```

And in general they call this rule the *modus monens*.

(but the lambda-calculus expression is more explicit, e.g. about the meaning of the
"horizontal bar" and also the quantification of `A` and `B`).

This is another extremely important component of (any) logic, and as we see this
is completely equivalent to another extremely important component of (any) programming
 language: *function application*.

### The Curry-Howard correspondance

What we just experienced in the previous section was discovered (partially) by Haskell Curry
 and later more concretely explained by William A. Howard (but then refined by many
 others). It is (hence) named the *Curry-Howard correspondance* between:

 - types and terms of a lambda-calculus on the one, computational, side

 - propositions and proofs on the other, logical, side

When we gave a logical reading for lambda-terms in the previous sections, we used:

  - *Propositions-as-Types* (e.g. suppose an arbitrary proposition `A`)

  - *Proofs-as-Terms* (e.g. suppose we have a proof `v` of `A`)

This is the *PaT* (or maybe more accurately *PaT-PaT*) interpretation of a (typed) lambda-calculus,
 and it is at the heart of LaTTe.

To provide a slightly more advanced example of the interest and use of the *PaT* interpretation,
 we will consider once more the pairing function.
 
In Clojure it was defined as follows:

```clojure
(fn [x] (fn [y] (fn [z] ((z x) y))))
```

We can give an explicit version in LaTTe, as follows:

```clojure
(lambda [A :type]
  (lambda [B :type]
      (lambda [x A]
           (lambda [y B]
        (lambda [C :type]
           (lambda [z (==> A B
                           C)]
                    ((z x) y)))))))
```
(wow! that's verbose...)

The type of this function is more interesting:

```clojure
(forall [A :type]
  (forall [B :type]
    (==> A B
        (forall [C :type]
          (==> (==> A B
                  C)
              C)))))
```
(wow! that's also verbose...).

To simplify a little bit matters, let's now suppose we have the
types `A` and `B` implicit (we'll see later how to make them *parameters*), so we drop 
the first two `lambda`'s and get for the pairing function:

```clojure
(lambda [x A]
    (lambda [y B]
       (lambda [C :type]
           (lambda [z (==> A B
                           C)]
               ((z x) y)))))))
```

The type becomes:

```clojure
(==> A B
     (forall [C :type]
        (==> (==> A B
                  C)
             C)))
```

That's a little bit more readable... but we will write
this even more concisely by naming `(pair A B)` the
 `(forall [C :type] ... C)` subexpression. We get:

```clojure
(==> A B
     (pair A B))
```

Now let's take the function `fst`:

```clojure
(fn [p] (p (fn [x] (fn [y] x))))
```

which becomes (still abstracting from `A` and `B`):

```clojure
(lambda [p (pair A B)]
    (p (lambda [x A]
          (lambda [y B]
              x))))
```

The type of the term, once again more interestingly, is:

```clojure
(==> (pair A B)
     A)
```

So `fst` is a function that takes a pair of an `A` and a `B`, and
yield an `A`, that's what we expected of course!

And you might then guess what the type of `snd` is:

```clojure
(==> (pair A B)
     B)
```

From a `(pair A B)` it yield a `B`.

Now let's apply the *PaT* interpretation. Because logical names
 are often far from computational ones, let's replace `(pair A B)`
  by `(and-by-all-means A B)` (but there is no trick here, it is just
   an alternative name for the same *thing*).

The type of the pairing function becomes:

```clojure
(==> A B
     (and-by-all-means A B))
```

Which, from a logical point of view, reads as follows:

This reads:

> - If we know that `A` is true and `B` is true
> - Then the conjunction of `A` and `B` is true.

In what is called *natural deduction* in logic this is exactly the definition of
 the *introduction rule for conjunction*.
 
Let's now take the `fst` function, whose type becomes:

```clojure
(==> (and-by-all-means A B)
     A)
```

So:

> If we know that the conjunction of `A` and `B` is true
> Then `A` "alone" is true

This is the *left elimination rule for conjunction* in natural deduction,
 and of course the right elimation rule of conjunction is demonstrated
 by the `snd` function of type:

```clojure
(==> (and-by-all-means A B)
     B)
```
 
So what we reconstructed here, using only the lambda-calculus and LaTTe, is the
common logical characterization of conjunction in natural deduction with its
 introduction and elimination rules.
 
We can go very far based on the Curry-Horward correspondance, and essentially all
 of logic and (arguably) mathematics can be built using a similar process.


At least it is hoped that the previous examples provide a good illustration of
 the deep connection existing between computation (types, expressions, function application)
 and reasoning (propositions, proofs, deduction) in a typed lambda-calculus.

It is now time to be a little bit more explicit about the particular calculus
implemented in LaTTe.


## The Calculus of Constructions (a.k.a. λC)

At the lowest-level of the LaTTe kernel sits a relatively simple
although very expressive lambda-calculus. It is an implementation
 of the *Calculus of Constructions* (first defined by *Thierry Coquand*)
  and often called *λC* nowadays. 
  
Remark: it is not impossible, but difficult, to write low-level lambda
 terms in LaTTe. This is both to be as faithful as possible to the theory and
  also to avoid working with low-level terms directly (they are somewhat
   unreadable even for the trained mind). Thanksfully, LaTTe also provides a 
   *parser* for higher-level terms, the ones manipulated by the users.

Some lambda-calculi are untyped, other ones make a clear distinction between terms
 on the one side, and types on the other side. This is *not* the case with λC, although
 some terms are types and others are not (of course !). We will see how to distinguish them.
 
A (low-level) lambda-term in LaTTe is either:

  - the constant: `✳` named **type**
  
This corresponds to the *type of types*. A lambda-term is said a *proper type* if its type is `□`. In the concrete syntax `□` is more conveniently written `:type`.

  - the constant  `□` named **kind**

This is to give a type to `□` (`:type`). The type of `□` is `□` (or `:kind` in the concrete syntax) and `□` *has no type*. For the sake of logical consistency, it is important that the type hierarchy stops somewhere, and it stops at the kind level (it is possible to introduce universes so that the hierarchy doesn't stop while preserving consistency, however for the sake of minimalism LaTTe doesn't need nor use universes... It is then said *impredicative*, which is nothing similar to a disease).

  - a  **lambda-abstraction** `(λ [x T] e)` with `x` the name of the **binding variable**, `T` a term corresponding to the type of `x` and `e` a lambda-term called the **body** of the abstraction

This is as we largely discussed the (single-argument) function constructor. In the concrete syntax, the most common notations are as follows:

```clojure
(lambda [x T] e) ≡ (λ [x T] e)

(lambda [x1 x2 ... xN T] e)
≡ (λ [x1 T] (λ [x2 T] ... (λ [xN T] e) ... ))
```

  - a **product-abstraction** (a.k.a. *Π-type*) `(Π [x T] e)` (with `x`, `T`, `e` as in the lambda case)

The *Π-types* are probably the most distinguishing feature of type theories such as *λC*. These simply are the *types* of the lambda-abstractions.

If a lambda-term `e` has type `U` in the context that `x` is of type `T`, then the type of `(λ [x T] e)` is `(Π [x T] U)`.

In the concrete syntax, the most common used notations are as follows:

```clojure
(forall [x T] U) ≡ (Π [x T] U)

(forall [x1 x2 ... xN T] U)
≡ (Π [x1 T] (Π [x2 T] ... (Π [xN T] e) ... ))
```

Yes, of course! This is the *universal quantifier* of the logic.

Moreover, if in `(Π [x T] U)` the variable `x` does not occur freely in `U`, then
an equivalent notation is `(==> T U)`.  This is thus not only universal quantification but
*also* (as a specific case) the type of functions from `T` to `U` *and* the *implication* that
from `T` we can get `U`.

A syntactic shortcut allows to chain the implications:

```clojure
(==> T1 T2 T3) ≡ (==> T1
                      (==> T2 T3))

(==> T1 T2 T3 T4) ≡ (==> T1
                         (==> T2
                              (==> T4 T4)))

;; etc...
```

  - an occurrence of a **variable** `x`, `y`, `A`, `B`, etc.

The variables are for example introduced by the abstractions (they can also be introduced by parameteric definitions, as discussed later on). The type of each variable is to be found in what is called the *context* or *typing context*.

  - an **application** `[f e]` with `f` and `e` lambda-terms, informally `f` a function and `e` its argument

If `f` is is type `(Π [x T] U)` and `e` is of type `T` then `[f e]` is of type `U` and realizes through beta-reduction the application of the function `f` on argument `e`.

*Remark*: the non-standard use of square brackets is to distinguish at the syntax level the applications for the refence terms below... In the concrete syntax the parentheses may be used, the Lisp way as: `(f e)`. Since we know that all abstrations have a single argument, the following syntactic shortcuts are quite useful:

```clojure
(e1 e2) ≡ [e1 e2]  ;; if e1 is not a defined term
(e1 e2 e3) ≡ [[e1 e2] e3]
(e1 e2 e3 e4) ≡ [[[e1 e2] e3] e4]
;; etc.
```
  - a **reference** `(r e1 ... eN)` with `r` the name of a **defined term** and `e1` ... `eN` lambda-rterms intended as arguments.

The references correpond to an extension of the calculus of constructions by *definitional features*, and it gives a calculus named *λD*. The idea is to have a term that references either a definition, an axiom or a theorem. 

If a term references a definition, then the definition is simply unfolded as in calling a function.

For example, the definition of conjunction in LaTTe (cf. [[latte.prop/and]]) is as follows:

```clojure
(definition and
  "logical conjunction."
  [[A :type] [B :type]]
  (forall [C :type]
    (==> (==> A B C)
         C)))
```

So a term such as `(and (> x 3) (<= x 8))` is equivalent to:

```clojure
(forall [C :type]
  (==> (==> (> x 3) (<= x 8) C)
       C))
```

The type of the reference is the same as the type of the unfolded term.

In the case of an axiom, the reference is considered similar to a constant, except with
 the parameters replaced by the arguments. The most famous (and sometimes controversed) axiom is probably the
law of the *excluded middle* of classical logic. It is defined as follows in LaTTe (in [[latte.classic]]):

```clojure
(defaxiom excluded-middle-ax
  "..."
  [[A :type]]
  (or A (not A)))
```

So for example a reference `(or (> x 3) (not (> x 3)))` can be considered inhabited (hence true), even though
 there is no underlying lambda-calculus term.

In the case of a theorem, then it is a little bit the same except that if a proof term is available then 
we could, in theory, consider the theorem as a definition and replace the reference term by the proof.

For exemple, based on the following theorem and proof (from [[latte.prop]]):

```clojure
(defthm impl-ignore
  "A variant of reflexivity."
  [[A :type] [B :type]]
  (==> A B A))

(proof impl-ignore
    :term (lambda [x A] (lambda [y B] x)))
```

The term `(impl-ignore (> a 2) (<= b 10))` could be replaced
by the following term:

```clojure
(lambda [x (> a 2)]
  (lambda [y (<= b 10)]
     x))
```

However, in practice, the references for theorems are not unfolded because
 it is useless since we already know the type of the proof term. Otherwise,
 the proofs that reference many theorems would yield very large proof terms.

### Fundamental properties

We now discuss the fundamental properties of the calculus of constructions
 with definitions that is implemented in LaTTe. These properties are
  important requirements when considering the formalization of logic.

First, let's remind that the syntactic equality of lambda-terms is governed by
 *alpha-conversion*, and the semantics are driven by *beta-reduction*.

The first important property of the calculus is what is called **strong normalization**.

TODO :

- a term is said in *normal form* iff there is not any redex.

- weak normalization means that if from a given term two normal forms are reached,
 then these must be alpha-convertible. Show two distinct strategies for `(snd ((pair "hello") 42))`.

 - but in e.g. the untyped lambda-calculus, there are terms with no normal forms.

 - and with some strategies, some normal forms cannot be reached

- strong normalization is weak normalization + all terms have a normal form

The second important property is the **decidability and uniqueness of typing**.

In LaTTe if a term has a type, then it is unique (up-to beta-equivalence). Moreover,
 given a term we can compute its type (if it has one). This is a very powerful feature,
  which is only rarely present in proof assistants based on type theory.

