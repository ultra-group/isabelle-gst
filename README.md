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

## Instructions for using our development:

### Pre-requisites:

1. Isabelle 2021-1: 

Our development is built in Isabelle/HOL,
  using the 2021-1 version of Isabelle.
Installation instructions and documentation
  can be found on the 
  [Isabelle webpage](https://isabelle.in.tum.de/).

2. A clone of the 
    [Archive of Formal Proofs](https://www.isa-afp.org/download.html) 
   (AFP):

We use Paulson's ZFC_in_HOL to bootstrap our development, 
  which is an entry in the AFP.
The [recommended instructions](https://www.isa-afp.org/using.html)
  for using the AFP in developments consist of making
  the entirety of the AFP available to Isabelle.

Download `afp-current.tar.gz`, then unzip into an appropriate directory `DIR`.   
  - For UNIX based systems:
  ``isabelle components -u DIR/afp-YYYY-MM-DD/thys``
  - For Windows 10 using Cygwin, if `DIR` is on drive `DRIVE`:
      ``isabelle components -u /cygdrive/DRIVE/DIR/afp/thys``


### Installing and building Isabelle/HOL/GST: 

1. Clone and this repository: 
  ``git clone git@github.com:ultra-group/isabelle-gst.git``
   or alternatively using HTTPS:
  ``git clone https://github.com/ultra-group/isabelle-gst.git``
   then navigate to the directory:
  ``cd isabelle-gst``  

2. Build heap images:
  ``make build-heap``

3. To open the development in Isabelle/jEdit, run:
  ``isabelle jedit -l GST``
  Alternatively load Isabelle/jEdit, and open one of the files in `src/`   

### Building HTML for browsing:

To build the HTML for viewing in a web browser, run:
  ``make build-html``    