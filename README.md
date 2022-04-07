# Isabelle/GST

A generalized set theory is an axiomatic theory that specifies a domain 
containing traditional ZF-style sets, and other kinds of non-set objects.
For a discussion of the preceding work, please see:

- [Generating Custom Set Theories with Non-Set Structured Objects](https://pure.hw.ac.uk/ws/portalfiles/portal/45486933/zf_plus_paper.pdf).
  Dunne, Wells, Kamareddine, 2021. 

This development extends Isabelle/HOL with a framework for:

- specifying GSTs as type-classes which may be instantiated by Isabelle/HOL types
- building and reasoning about models of GSTs within other GSTs 
- lifting models of GSTs into fresh types

## Background
**Sets** capture the notion of a *collection of mathematical objects*.
  - In Isabelle/HOL: for every type `α` there is the type 
      [`set α`](https://isabelle.in.tum.de/library/HOL/HOL/Set.html#Set.set|type)
    which is essentially the type of unary predicates on `alpha` (i.e., `α ⇒ bool`).
    In this context, a set is any member of a type `set α`, for some type `α`.

  - In Isabelle/ZF: there is a type 
      [`i`](https://isabelle.in.tum.de/library/ZF/ZF/ZF_Base.html)
    axiomatized as the domain of discourse of Zermelo-Fraenkel set theory.
    In this context, a set is any member of the type `i`.

Only a few types are used in the development of Isabelle/ZF.
(`i` for sets, `i ⇒ i` for operators on sets, `i ⇒ o` for predicates on sets, etc.)
Objects like [ordered pairs](https://isabelle.in.tum.de/library/ZF/ZF/ZF_Base.html#ZF_Base.Pair|const), 
[functions](https://isabelle.in.tum.de/library/ZF/ZF/ZF_Base.html#ZF_Base.function|const), 
and [natural numbers](https://isabelle.in.tum.de/library/ZF/ZF/Nat.html#Nat.nat|const), 
are all defined as sets.  

Some set theories (ZFU, KPU) have **non-set objects** called urelements,
which have no set members, and can belong to sets.
Urelements are often only used for esoteric purposes.  

- A set is **pure** if it is the empty set, if all of its members are pure sets.
- A set is **impure** if it is not pure.
- A **generalized set theory** (GST) is a theory that has pure sets 
  and may also have non-sets that can have internal structure 
  and impure sets that mix sets and non-sets.