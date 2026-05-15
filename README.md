# R1R2proof

A standalone Lean 4 development of the R1/R2 residual-mediation framework,
with formula-level Peano arithmetic and ZFC instances, exact dimension-2 PA
certificates, and finite exact-dimension ZFC certificates.

The project does not import mathlib.  It is intended to be auditable as a
small standalone Lake project.

## Core Notation

```text
R1-identity:
  x ≡ᵢ y

R2-fracture:
  sigma(x) and sigma(y) are distinct

M-refined identity:
  x ≡ᵢ,ₘ y := x ≡ᵢ y and M(x) = M(y)
```

In Lean, the notation is parameterized explicitly:

```lean
x ≡ᵢ[obs, I] y
x ≡ᵢ,ₘ[obs, I, M] y
```

## Main Theorem

The repository formalizes a structural distinction between two regimes:

```text
R1: explicit closure of a presentation.
R2: local closure of required distinctions by certified mediation.
```

In the Peano arithmetic instance, PA is represented as first-order formula
syntax, not as informal labels and not as Lean axioms.  The syntax includes:

```text
0, S, +, *
equality, negation, implication, conjunction, universal quantification
six standard first-order PA axiom formulas
the induction schema
```

The content is the relative obstruction:

```text
The R1 trace projection identifies the relevant PA family data while leaving
the base/step coordinate unresolved.

This unresolved coordinate forms a diagonal R2 residual.

The exact proper mediated R2 dimension of this residual is 2.
```

Equivalently: the theorem is not the bare existence of a map into `Fin 2`, nor
the observation that a base/step pair can be encoded by two values.  It proves
that, relative to the chosen R1 trace projection, the base/step coordinate
survives as an R2 residual, and that the smallest proper mediated closure of
this residual has exact finite dimension `2`.

In the PA instance, this exact dimension is realized by the phase mediator.
The mediator matters because it is certified as minimal relative to the R1
trace projection, not because `Fin 2` is by itself a surprising codomain.

This is a syntactic structural theorem about PA formula objects and formula
components.  Its intended role is to certify a residual-mediation phenomenon
inside a standalone Lean development.  It is not a claim that PA is
semantically false, and it is not a complete formalization of first-order proof
theory or model theory.

## Finite Dimension Hierarchy

The framework is not tied to the binary PA base/step case.

`FiniteDimensionHierarchy.lean` proves that exact mediated R2 dimensions occur
in every finite dimension `n >= 2`.  For each such `n`, it constructs a finite
R1/R2 instance whose exact proper mediated R2 dimension is exactly `n`.

The structure of the proof is:

```text
R1 identifies all states through a trivial trace.

R2 requires distinct states to remain distinct.

Any mediator closing the residual must separate all states.

Therefore any mediator into Fin m induces an injection Fin n -> Fin m.

If m < n, such an injection is constructively impossible.

Dimension n is achieved by the identity mediator Fin n -> Fin n.
```

So the PA base/step certificate is one structured dimension-`2` instance of a
general finite hierarchy.  The broader invariant is:

```text
R2 mediation measures the minimal finite dimension needed to separate the
residual left by an R1 projection.
```

## ZFC Formula Instance

`ZFCFormulaAxioms.lean` formalizes ZFC in the pure first-order language of set
theory:

```text
variables
equality
membership
logical connectives
universal and existential quantification
```

It defines the standard ZFC axiom formulas as syntax, including
Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, Separation,
Replacement, Foundation, and Choice.

The R1/R2 certificate in the same file operates on formula-bearing objects:

```text
ZFCFormulaAxiom
ZFCFormulaComponent
ZFCAllAxiomFiniteState n
```

For every `n >= 2`, the full ZFC carrier contains every certified ZFC axiom
object and finite families of actual Separation and Replacement formula
components.  These finite states are not arbitrary formula/coordinate pairs:
the formula is determined by the Separation or Replacement constructor and its
finite coordinate.  Full ZFC axioms are present as certified formulas, without
receiving arbitrary finite labels.  The R1 interface uses separate family and
component-role readers, so the irreducibility statements apply to the isolated
family-only and role-only marginal subfamilies.  The file proves:

```text
exactMediatedR2Dimension_n_ZFC_finite
exactProperMediatedR2Dimension_n_ZFC_finite
exactMediatedR2Dimension_n_ZFC_replacement_finite
exactProperMediatedR2Dimension_n_ZFC_replacement_finite
exactMediatedR2Dimension_n_ZFC_all
exactProperMediatedR2Dimension_n_ZFC_all
```

So the ZFC section gives exact mediated R2 dimension `n`, and also exact
proper mediated R2 dimension `n`, on carriers that still contain the
syntax-level ZFC axiom presentation.

## What Is Formalized

The static kernel in `RegimesSelfContained.lean` defines:

```text
DiagonalizationWitness
Residual_R2
ResidualEmpty_R2
ResidualNonempty_R2
Closed_R2
MediatedResidualEmpty
IrreducibleMediator
WitnessedIrreducibleMediator
ProperMediatedR2Certificate
ExactProperMediatedR2Dimension
```

It also proves the core equivalences between direct closure, residual
emptiness, mediated residual closure, witnessed irreducibility, and exact
finite mediated dimension.

The dynamic kernel in `DynamicRegimesSelfContained.lean` extends the same
framework with:

```text
step-indexed targets
uniform mediated certificates
dynamic exact mediated dimensions
dynamic residual profiles
stable residual sections
dynamic closure bridges
```

The Peano files instantiate the framework on actual PA formula syntax.

## Peano Formula-Level Instance

`PeanoPAFormulaAxioms.lean` defines the first-order language of PA:

```lean
inductive Term
  | var : Nat -> Term
  | zero : Term
  | succ : Term -> Term
  | add : Term -> Term -> Term
  | mul : Term -> Term -> Term

inductive Formula
  | falsum : Formula
  | equal : Term -> Term -> Formula
  | not : Formula -> Formula
  | imp : Formula -> Formula -> Formula
  | and : Formula -> Formula -> Formula
  | forallE : Nat -> Formula -> Formula
```

It then defines the PA axiom formulas:

```text
forall x, S x != 0
forall x y, S x = S y -> x = y
forall x, x + 0 = x
forall x y, x + S y = S (x + y)
forall x, x * 0 = 0
forall x y, x * S y = x * y + x
induction schema for a formula phi
```

The file proves two exact R1/R2 certificates:

```text
PAFormulaAxiom:
  full PA formula axioms, including the induction schema

PAFormulaComponent:
  formula components exposing base/step structure, including induction_base
  and induction_step for a formula parameter
```

Both certificates have exact proper mediated R2 dimension `2`.

## Dynamic Peano Instance

`PeanoPAFormulaAxiomsDynamic.lean` imports the dynamic kernel and the static PA
formula instance.

It provides:

```text
stable dynamic lift of the PA formula axiom certificate
active step-indexed dynamics for addition and multiplication axiom pairs
active component dynamics for addition, multiplication, and induction
temporal residual profiles
raw stable residual sections
mediated temporal residual closure
dynamic exact proper mediated dimension 2
```

The dynamic target is nontrivial in the formal sense that the step selects the
active target, active pair, mediator behavior, and residual profile.  It is not
an empirical learning system and does not encode a historical world-model
training process.

## Dynamic LLM/R1R2 Alignment Instance

`LLMAlignmentDynamicR1R2.lean` instantiates the dynamic R1/R2 framework on an
abstract causal-trajectory alignment carrier.

For every `n >= 2`, every dynamic step has exact proper mediated R2 dimension
`n`.  The dynamic target reads a step-relative injective transform of the
trajectory coordinate, and the mediator reads the same coordinate.

The file also separates full trajectory mediation from Boolean compatibility
classification:

```text
trajectory mediation dimension      = n
compatibility classifier dimension  = 2
```

The file defines `Aligned h`, a formal alignedness predicate for the abstract
dynamic carrier, and proves:

```text
endToEnd_aligned_alignment
```

It also defines `ExternalAlignmentBridge`, a bridge from an external carrier
to the formal R1/R2 trajectory interface.  A bridge supplies raw states, raw
steps, an observed raw step, a finite causal coordinate, representatives for
every coordinate, and injective step transforms.  From such a bridge the file
proves:

```text
externallyAligned_of_bridge
externallyAligned_observedStep_of_bridge
exactProperMediatedR2Dimension_n_external_observedStep
```

The current external bridge models the observation-only collapse case:
terminal and prompt observations are constant over `RawState`.  The exact
dimension result therefore concerns the residual left by visible
terminal/prompt observation when the finite causal coordinate is not read.

This Lean theorem is structural.  Empirical ASLMT work supplies evidence only
by constructing or approximating such a bridge for concrete logs or systems.

## File Map

```text
R1R2proof.lean
  Root module importing the static kernel, dynamic kernel, and Peano instances.

RegimesSelfContained.lean
  Static standalone R1/R2 framework.

DynamicRegimesSelfContained.lean
  Dynamic standalone R1/R2 framework.

R1R2Notation.lean
  Lean notation layer for observational identity, R2 fracture, and mediated
  identity.

FiniteDimensionHierarchy.lean
  Parametric exact-dimension family: for every n >= 2, a finite R1/R2
  instance with exact proper mediated R2 dimension n.

PeanoPAFormulaAxioms.lean
  Static formula-level PA instance and exact dimension-2 certificates.

PeanoPAFormulaAxiomsDynamic.lean
  Dynamic and temporal formula-level PA instance.

ZFCFormulaAxioms.lean
  Syntax-level ZFC axiom formulas in the pure first-order language of set
  theory, including Separation, Replacement, and Choice, plus finite
  exact-dimension R1/R2 certificates on formula-bearing ZFC carriers.

LLMAlignmentDynamicR1R2.lean
  Dynamic alignment carrier, exact trajectory mediation dimension n, Boolean
  compatibility dimension 2, and external bridge theorem for raw systems with
  finite causal coordinates.

ZFC_formula_axioms_spec.md
  Specification for the single-file ZFC formula-level target and its R1/R2
  certificate section.

Local_closure_regimes.md
  Conceptual note explaining R1, R2, residuals, and mediated closure.

Foundational_questions.md
  Status note for PA and set-theory questions.

Notation.md
  Notation for observational identity, mediated identity, and exact finite
  refinement.

R1_categorical_diagrams.md
R2_categorical_diagrams.md
  Diagrammatic explanations of the two regimes.
```

## Verification

The project uses:

```text
Lean 4.29.1
Lake
```

Build:

```bash
lake build
```

The Lean files include `#print axioms` audit blocks for the main definitions
and theorems.  A successful build prints that the audited declarations do not
depend on any axioms.

## Scope

This repository proves a self-contained structural certificate:

```text
R1 trace projection:
  sees PA formula families and parameters.

R2 residual:
  exposes base/step distinctions not separated by that R1 trace.

R2 mediator:
  separates the residual with a Fin 2 coordinate.

Exact dimension:
  no proper mediated certificate exists in dimension 0 or 1;
  dimension 2 is achieved.
```

It also contains a parametric finite hierarchy:

```text
for every n >= 2,
there is a finite R1/R2 instance with exact proper mediated R2 dimension n.
```

It also contains a ZFC formula-level instance:

```text
for every n >= 2,
finite ZFC Separation components, finite ZFC Replacement components, and the
full ZFC formula carrier containing both have exact mediated R2 dimension n
and exact proper mediated R2 dimension n.
```

The repository does not yet contain:

```text
a full formalized proof system for first-order logic
a model theory of PA
an empirical world-model implementation
```

Those are natural extension targets, but they are not claimed by the current
Lean development.
