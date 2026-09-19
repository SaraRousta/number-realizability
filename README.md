# Number Realizability

A machine-checked synthetic reconstruction of Kleene number realizability and an external version of Troelstra's characterization theorem in the Rocq proof assistant.

This development accompanies the master's thesis:

> Sara Rousta, *A Synthetic Reconstruction of Troelstra's Characterization of Number Realizability in Rocq*, September 2026.

## Mathematical overview

Kleene number realizability gives computational meaning to formulas of intuitionistic arithmetic. A formula is not interpreted merely as true or false: a natural number realizing the formula provides computational evidence for it.

For example:

- a realizer of a conjunction contains realizers of both conjuncts;
- a realizer of a disjunction contains a tag identifying the realized disjunct, together with its realizer;
- a realizer of an implication codes a partial function transforming realizers of the antecedent into realizers of the consequent;
- a realizer of an existential formula contains a witness and a realizer for the formula instantiated with that witness;
- a realizer of a universal formula codes a partial function producing a realizer for every natural-number input.

Traditional accounts express these computations using a concrete model of computation and explicit Gödel indices. This development instead uses synthetic computability. Partial functions are treated abstractly, while the Enumeration of Partial Functions axiom (`EPF`) supplies codes for the partial functions constructed in Rocq.

This makes it possible to work directly with functions in the Calculus of Inductive Constructions while retaining the usual recursion-theoretic interpretation of realizing numbers.

## Main results

The development formalizes four principal parts of the thesis.

### External number realizability

Kleene number realizability is defined directly in the metatheory for formulas of first-order arithmetic.

The formalization includes:

- realizability under variable assignments;
- realizability of contexts;
- finite encodings of environments;
- uniform realization of arithmetic terms;
- substitution and extensionality results for evaluation and realizability.

### Generalized soundness

The central soundness theorem is proved for intuitionistic natural deduction.

It is generalized over:

- the values assigned to the free variables;
- an encoding realizing that variable assignment;
- realizers of all formulas in the assumption context.

Thus, if `Γ ⊢ φ`, the proof produces a code for a computation that transforms a realized environment and a realizer of `Γ` into a realizer of `φ`.

The development then proves that the axioms of intuitionistic Robinson arithmetic `Q` and Heyting arithmetic `HA` are realizable. It also derives the corresponding soundness and consistency consequences.

### Markov's principle

The development distinguishes between arithmetic and metatheoretic forms of Markov's principle.

It proves, in particular, that:

- metatheoretic boolean Markov's principle suffices to realize the arithmetic Markov scheme;
- conversely, subject to countable choice, realizability of the arithmetic Markov scheme implies Markov's principle for predicates representable in Robinson arithmetic.

This reverse implication demonstrates that realizability of an object-theoretic principle can impose a corresponding principle on the metatheory.

### Almost-negative formulas and characterization

The standard syntactic class of almost-negative formulas is formalized, together with a corresponding notion of almost-negative predicates in the metatheory.

The development establishes:

- external self-realizability for almost-negative formulas;
- an almost-negative characterization of the realizability predicate;
- under the appropriate countable-choice and independence-of-premise assumptions, an equivalence between realizability and satisfaction in the standard model.

This gives an external synthetic reconstruction of Troelstra's characterization of number realizability.

## Project contents

The source files are listed below in dependency order.

### `LogicalFacts.v`

Contains basic logical principles and equivalences used by the realizability development.

### `Core.v`

Defines evaluation of arithmetic terms, number realizability under a variable assignment, and realizability of a context.

### `Facts.v`

Establishes substitution, extensionality, and other general properties of evaluation and realizability, including characterizations of realizability for negation, double negation, and existential formulas.

### `RealizingEnvTerms.v`

Develops finite encodings and decoding of variable assignments, properties of realized environments, and uniform realization of arithmetic terms.

### `BoundedTactics.v`

Contains reusable boundedness lemmas and tactics used to discharge the free-variable conditions appearing in later results. The comments attached to the tactics identify the theorems for which they are intended.

### `Soundness.v`

Proves generalized soundness for intuitionistic natural deduction and derives the corresponding consistency result.

### `RealizingArithmetic.v`

Constructs realizers for the nonlogical axioms of arithmetic, including induction, and encodes realizers for the finite theory `Qeq`.

### `RealizingMP.v`

Studies realizability of the arithmetic Markov scheme from metatheoretic boolean Markov's principle.

### `AlmostNegative.v`

Defines almost-negative arithmetic formulas and proves their external self-realizability properties.

### `Sigma1Realizability.v`

Connects realizability with the existing definitions and results for `Qdec` and `Σ1` formulas from `FOL.Incompleteness`, relating truth in the standard model, provability in Robinson arithmetic, and existence of a realizer.

### `QRepresentableMP.v`

Studies Markov's principle for predicates representable in Robinson arithmetic and proves the reverse implication from realizability of the arithmetic Markov scheme.

### `Characterization.v`

Defines an almost-negative computational predicate equivalent to the realizability relation and proves the external characterization theorem.

## Dependencies

The project builds on two existing Rocq developments:

- the FOL library for first-order syntax, arithmetic, natural deduction, standard-model semantics, boundedness, substitution, and `Σ1` results;
- Synthetic Computability for abstract partial functions, coding of partial functions, and the `EPF` principles.

It also uses the Rocq standard library and the Equations plugin. The FOL and Synthetic Computability libraries must be installed and visible in the active opam switch.

## Tested configuration

The project has been compiled successfully in the following environment:

| Component | Version |
| --- | --- |
| Rocq executable | 9.0.1 |
| OCaml | 4.14.0 |
| Rocq standard library | 9.0.0 |
| Equations | 1.3.1+9.0 |
| VSCoq language server | 2.4.3+1 |
| opam switch | `rocq9.0-synthetic-realizability` |

The Rocq executable reports:

```text
The Rocq Prover, version 9.0.1
compiled with OCaml 4.14.0
```

This is the configuration in which the complete project has been tested. 

## Building the project

Clone the repository together with its CoqdocJS submodule:

```sh
git clone --recurse-submodules git@github.com:SaraRousta/number-realizability.git
cd number-realizability
```

If the repository was cloned without its submodules, retrieve them afterwards with:

```sh
git submodule update --init --recursive
```

Activate the tested opam switch e.g.:

```sh
opam switch rocq9.0-synthetic-realizability
eval "$(opam env)"
```

Compile the project:

```sh
make -j2
```

The permanent `Makefile` automatically generates `Makefile.coq` from `_CoqProject` when necessary and then delegates compilation to it. The option `-j2` permits up to two independent compilation jobs to run in parallel. Use `make` for sequential compilation.

For a clean rebuild:

```sh
make clean
make -j2
```

## HTML documentation

Generate browsable HTML documentation with:

```sh
make html
```

The documentation is written to the generated `html` directory. CoqdocJS provides improved navigation, configurable Unicode display, and proofs that are collapsed by default and can be expanded by clicking `Proof...`.

Open the local documentation homepage with:

```sh
xdg-open html/index.html
```

Each declaration receives a stable HTML anchor. For example, the generalized soundness theorem is available locally at:

```text
html/NumberRealizability.Soundness.html#realizes_sound_ND
```

The generated `html` directory is not committed because it can be reproduced from the Rocq sources and will be published separately through GitHub Pages.


## Logical namespace

The `_CoqProject` file assigns the standalone logical namespace:

```text
-Q . NumberRealizability
```

Internal project imports therefore have the form:

```coq
From NumberRealizability Require Import Core Facts.
```

Dependencies belonging to the external FOL development retain their original namespace:

```coq
From FOL Require Import FullSyntax Arithmetics.
From FOL.Incompleteness Require Import qdec sigma1.
```

## Relationship to the thesis

The Rocq development principally corresponds to Chapters 4 and 5 of the thesis:

- Chapter 4 develops external number realizability, its administrative machinery, generalized soundness, and the `Σ1` results;
- Chapter 5 studies Markov's principle, almost-negative formulas, self-realizability, and the external characterization theorem.

The earlier thesis chapters provide the necessary background on the Calculus of Inductive Constructions, synthetic computability, first-order arithmetic, and the traditional internal development of number realizability.

## Development assistance

ChatGPT was used to assist with reorganizing the original already complete Rocq development into a standalone project, reviewing naming and file structure, diagnosing compilation errors during the reorganization, preparing the build and documentation configuration, and drafting parts of this README. 

