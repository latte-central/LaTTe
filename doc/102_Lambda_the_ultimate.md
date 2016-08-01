
# Lambda the ultimate

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

The church thesis is that everything computable can be expressed with similar
encodings in such a "simple" lambda-calculus. While most introductions provide long lists
 of encodings of things such as booleans, numbers, arithmetic operations, (etc.), we
  will *not*. The thing is, such encodings are not practical, they yield very slow
   computations. But this does not remove any interest of the lambda-calculus in
    the practice of programming: what would be Clojure without `fn` ?

Before dwelving into the main subject, we have to introduce (or remind of) two
important features of the lambda-calclus: *alpha-conversion* and *beta-reduction*.

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

The question *Why types?* is one of the greate debates of programming. Clojure
 programmers obviously made a choice of relying on types at runtime (a.k.a. dynamic
  typing) instead of at compile-time (a.k.a. static typing). As a consequence, the
  lambda-calculus embedded in Clojure is itself of an *untyped* nature.
  
The expression `(fn [x] x)` does not contains any explicit (nor implicit) type information.
 The Clojure compiler does not perform any type-checking when encoutering such an expression.
  
From a logical perspective, the question *Why types?* is also a debate
 but as far as the lambda-calculus is concerned, the question is more
 of the kind: *What kind of types?*.  LaTTe implements a very strongly
 and very explicitely typed lambda-calculus. Suppose we have a type `A`, then the
 identity function for type `A` can be written in LaTTe as follows:

```clojure
(lambda [x A] x)
```

The `lambda` keyword is of course the `fn` of LaTTe. The variable `x` is explicited
 of having type `A`.

of the identity function
must be typed, here by a type name `A`. But the latter must also by typed, which we do
by explaining that `A` should be itself of type `:type`, the *type of types*.

If we want to use this identity function, we have to provide two arguments, as in:

```clojure
(((lambda [A :type] (lambda [x A] x)) int) 42)
--> ((lambda [x int] x) 42)
--> 42
```

A first remark is that things are now much more verbose than in the untyped case.
A second remark is that a type `int` was use as a value, and there's nothing strange
about this.

A question we might now ask is: what is the type of the identity function ?

The term describing the identity function was:

```clojure
(lambda [A :type] (lambda [x A] x))
```

And its type can be also written as a term in LaTTe:

```clojure
(forall [A :type] (==> A A))
```

The term above has a straightforward logical explanation:

> for any proposition A, it is true that A implies A

This is also called the *reflexivity of implication*, and it is a simple albeit important
property of logic.

What we have here is a lambda-calculus type whose meaning is a logical proposition.
This is the *Propositions-as-Types* (PaT) interpretation of lambda-terms.

Obviously, the proposition above should be true, and we might want to prove it... But in
 fact we already proved it because we have a term whose type is the proposition: this is the
 identity function!
 
So the reflexivity of implication is demonstrated by the (generic) identity function!
This is the *Proofs-as-Terms* (PaT) interpretation of lambda-terms.

The PaT-PaT interpretation of lambda-calculus is at the heart of the famous
Curry-Howard correspondance.

In logic propositions come first, and proofs next. Thus in LaTTe we first express types (hence propositions),
 and then tries to find terms (hence proofs) having these types.
 
Let's try with a slightly more complex proposition.

```clojure
(forall [A :type]
  (forall [B :type]
    (==> (==> A B)
	     A
		 B)))
```

This proposition says that if I now that `A` implies `B`, and moreover that `A` is true,
 then in conclusion `B` should be true also. This is the famous *modus ponens* written as a lambda-term.
 
Let's find a term inhabiting this type... that's not too difficult but maybe requires some practice.
Anyways, here's the answer.

```clojure
(lambda [A :type]
  (lambda [B :type]
     (lambda [H1 (==> A B)]
	   (lambda [H2 A]
	      (H1 H2)))))
```
In the term above `H1` is of type `(==> A B)` which means, from a
lambda-calculus perspective, that `H1` is a function from type `A` to type `B`.
Moreover, `H2` is a value of type `A`. Hence, to have a value of type `B`, 
an obvious thing to do is to apply `H2` to `H1`.

One possible reading of the term above is that we have a function that takes 
two types `A` and `B`, and yield 
a function taking two arguments, an argument `H1` of type `(==> A B)`, a second argument
`H2` of type `A`, and returns a value of type `B`. This is exactly describing
 the type that was our starting point.

### The core calculus

TODO

### Strong normalization

TODO: low-level vs. high-level terms

### Uniqueness of typing


## On dependent types

### Terms depending on terms

### Terms depending on types

### Types depending on types

### Types depending on terms
