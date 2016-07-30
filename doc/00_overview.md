
# Overview

**LaTTe** is a proof assistant designed as
a library for the Clojure programming language and environment.

It is based on a simple dependent-typed lambda-calculus.

LaTTe has been developed, and is currently maintained by F. Peschanski.

It is available under the MIT License (cf. `LICENSE` file in the
source repository).

This documentation contains reference material (auto-generated from
 the source code) as well as some background and tutorial informations.
 
 
## Background information
 
This background information is not required but recommended reading for using LaTTe.
 
  - A logician dream, providing some historical information about the
	formalization of mathematics and proof assistants (can be boring...)
	
  - **Lambda the ultimate**, explaining the
  resemblance and difference between the lambda-calculus
   found as a subset of modern programming languages
   (esp. Clojure) and the lambda-calculus used in LaTTe.
   
  - the architecture of a proof assistant explains the
  basic architecture of proof assistants based on type
   theory and gives some more details about how LaTTe is
   working underhood.
   
  - a short comparison with other proof assistants is also proposed.
  
  
Note that the design of LaTTe has been heavily influenced by the book :

> Type Theory and Formal Proofs - an Introduction
> by Geuvers and Nederpeldt.
> (Oxford University Press)

It is clearly a recommended (but not required) reading, especially
 for the design of the basic library of definitions, theorems, etc.
 
## Tutorial documents

The following are recommended readings for LaTTe beginners.
Most of these documents assume a certain familiarity with
the Clojure programming language and environment. They generally
 adopt the point of view of a programmer.

  - A proposition primer, because that's a good start. Most of the
    important concepts of LaTTe are introduced and illustrated in this document.
  
  - The indiscernibility of equals provide some important information
  about one particularly tricky (and highly debated) aspect of type theory.

  - Quantifiers unleashed explains how to work with universals, existentials 
   and definite elements (and this last one is new for most people).
   
  - A proof script tutorial, focuses on what is arguably the most important
    feature of LaTTe: a DSL for proving theorems.
	
  - Definining specials explains a powerful (if somewhat tricky) feature
   of LaTTe, that allows to generate terms (e.g. proof steps) dynamically. 
	

## Reference material

  - The [[latte.core]] namespace provide the main top-level forms of the LaTTe environment.

The **basic LaTTe library** provides a rather minimal logical and mathematical theory upon which
(arguably) most of mathematics can be built. This basic library only allows very "low-level" mathematical
 reasoning (whatever that means!). External LaTTe libraries are required for
	more serious work.

  - The [[latte.prop]] namespace for basic propositions.

  - The [[latte.equal]] namespace for Leibniz's equality.
  
  - The [[latte.quant]] namespace for reasoning with quantifiers.
  
  - The [[latte.classic]] namespace for classical (as opposed to intuitionistic) reasoning.

  - The [[latte.subset]] namespace for (typed) set-theoretic concepts.

  - The [[latte.rel]] namespace for basic definitions concerning relations, functions and maps.

