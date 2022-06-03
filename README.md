# Isabelle/GST

A *generalized set theory* (GST) is like a standard set theory but also has non-set
  structured objects that can contain other structured objects including arbitrary sets.
For a discussion of the preceding work, please see:

- Isabelle/HOL/GST: A Formal Proof Environment for Generalized Set Theories.
  Dunne, Wells, 2022.
- [Generating Custom Set Theories with Non-Set Structured Objects](https://pure.hw.ac.uk/ws/portalfiles/portal/45486933/zf_plus_paper.pdf).
  Dunne, Wells, Kamareddine, 2021. 

This development adds Isabelle/HOL support for GSTs:
- *Features* that specify kinds of mathematical objects,
    defined as [classes](https://isabelle.in.tum.de/doc/classes.pdf)
    with some extra structure.
- *Combining features* to create GSTs, also as classes.
- *Model components* that specify schematics for building models of GSTs,
- Integration with [Lifting and Transfer](https://www21.in.tum.de/~kuncar/documents/huffman-kuncar-cpp2013.pdf)
  for connecting a model of a GST in a type dᵢ to another type dⱼ.  

<!-- ## Background
**Sets** capture the notion of a *collection of mathematical objects*.
  - In Isabelle/HOL: for every type `α` there is the type 
      [`set α`](https://isabelle.in.tum.de/library/HOL/HOL/Set.html#Set.set|type)
    which is essentially the type of unary predicates on `α` (i.e., `α ⇒ bool`).
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
  and impure sets that mix sets and non-sets. -->

## Installation Instructions

### Prerequisites

1. Isabelle 2021-1: 

Our development is built in Isabelle/HOL, using the 2021-1 version of Isabelle.
Installation instructions and documentation can be found on the 
  [Isabelle webpage](https://isabelle.in.tum.de/).

Make sure that the Isabelle binary is in your `$PATH` environment variable.

2. A clone of [ZFC_in_HOL](https://www.isa-afp.org/entries/ZFC_in_HOL.html):

We use Paulson's ZFC_in_HOL, which is an entry in Isabelle's Archive of Formal Proofs (AFP),
 to bootstrap our development. 
[Download](https://www.isa-afp.org/release/afp-ZFC_in_HOL-current.tar.gz)
  the entry and unpack the contents into an appropriate directory `DIR`.
Then make `ZFC_in_HOL` available to Isabelle:  
  - For UNIX based systems:
  ```
  isabelle components -u DIR/ZFC_in_HOL
  ```
  - For Windows 10 using Cygwin, if `DIR` is on drive `DRIVE`:
  ```
  isabelle components -u /cygdrive/DRIVE/DIR/ZFC_in_HOL
  ```

### Installing and building Isabelle/HOL/GST

1. Clone this repository: 
  ```
  git clone git@github.com:ultra-group/isabelle-gst.git
  ```
   or alternatively using HTTPS:
  ```
  git clone https://github.com/ultra-group/isabelle-gst.git
  ```
 
2. If you don't want to have to check `ZFC_in_HOL`, 
   then navigate to `isabelle-gst` and build heap images:
  ```
  cd isabelle-gst; make build-heap
  ```

3. Open a file in Isabelle/jEdit, using `ZFC_in_HOL` as a base logic. 
  For example:
  ```
  isabelle jedit -l ZFC_in_HOL src/GST_Features.thy
  ```
  Alternatively, open Isabelle/jEdit and manually change the logic:
  ```
  Plugins > Plugin Options > Isabelle > General > Logic > ZFC_in_HOL
  ```
  After changing logic, restart Isabelle/jEdit and open a file.  

### Building HTML for browsing

To build the HTML for output in `html/`, run:
  ```
  make build-html
  ```

## Entry Points

| File | Description |
|------|-------------|
| `GST_Logic.thy`   | Definition of the *definite description with a default* operator |
| `Soft_Types.thy`  | Definition of Soft Types, inspired by [Kappelmann/Krauss/Chen](https://github.com/kappelmann/Isabelle-Set) |
| `Tools/*.ML`      | Isabelle/ML code for building GSTs |
| `GST_Features.thy`| Definintion of GZF, Ordinal, OPair, Relation, Function, Exception features |
| `GZF/*.thy`       | Development of GZF feature |
| `Ordinal/*.thy`   | Development of Ordinal feature | 
| `OPair/*.thy`     | Development of OPair feature |
| `Function/*.thy`  | Development of Function feature |
| `Exception/*.thy` | Development of Exception feature |
| `Relations/*.thy` | Development of Binary Relation feature |
| `ModelKit/*.thy`  | Model building kit |
| `ModelKit/Tools/*.ML` | Isabelle/ML code for building models of GSTs |
| `Founder/ZFC_in_HOL_Bootstrap.thy` | Instantiating V as a GST |
| `Founder/Test.thy` | Building ZF⁺ in d₀ by building a model in V | 


## Usage

### Features & GSTs

1. To define a GST feature, first define a class of the form: 
```
class Foo = D₁ + ... + Dₙ +
  fixes 
    Foo_default :: 'a and 
    ...
  assumes 
    ...
```
  a. To perform reasoning from the axioms of a feature, 
     open the context of the feature's class by:
```
context Foo begin
...
end
```

2. Declare a feature as an ML value, specifying terms for logo and cargo types:
```
ML ‹val Foo = Feature
  { cla = @{class Foo}, deps = [GZF], 
    logo = @{trm ...}, cargo = @{trm ...},
    default_param = @{trm Foo_default} }›
```
3. Define a list of feature configurations: 
```
ML ‹val GST_spec = 
  [ {feat = Foo, default_val = @{term ...}, blacklist = [...]},
    {feat = Bar, default_val = @{term ...}, blacklist = [...]},
    {feat = Baz, default_val = @{term ...}, blacklist = [...]} ]›
```
4. Create a class for a GST called <NAME> by:
```
local_setup ‹snd o mk_gst "<NAME>" GST_spec› 
```