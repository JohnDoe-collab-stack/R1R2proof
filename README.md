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

## Gödel-Style Proof/Truth Bridge

`GodelR1R2Bridge.lean` formalizes the abstract bridge from proof-theoretic
undecidability to the R1/R2 language.  It does not prove Gödel's
incompleteness theorem.  Instead, it proves that once a Gödel-style local
proof/truth pair is supplied, it produces an R1/R2 residual.

The local bridge uses a sentence `delta` and its negation:

```text
R1 reads proof status.
R2 reads truth status.
delta and neg delta have the same R1 proof-status observation.
delta and neg delta have different R2 truth-status values.
```

The file proves:

```text
r2IndecidableForR1_of_localProofTheoreticIndecidable
residualNonempty_of_localProofTheoreticIndecidable
exactProperMediatedR2Dimension_two
endToEnd_godelPair
```

Thus the two-state Gödel pair gives:

```text
proof/truth R2 residual
mediated closure by Fin 2
exact proper mediated dimension 2
witnessed irreducibility
```

## Zorn R1/R2 Closure

`ZornR1R2.lean` does not reprove Zorn's lemma.  It takes the usual Zorn
conclusion as an external principle and rewrites it in R1/R2 notation.

The file proves:

```text
local R1/R2 closure at p  <->  p is maximal
```

It also adds the temporal layer.  A dynamic Zorn certificate is proved
equivalent to:

```text
static terminal R1/R2 closure + compatible trajectory data
```

So the dynamic certificate preserves the complete trajectory it claims to
carry.  A finite two-point example proves that forgetting the trajectory back
to the terminal-only certificate is not injective.

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
family-only and role-only marginal subfamilies.  The mediator is therefore a
joint mediator: it closes the R2 residual from the combined R1 trace, while it
does not descend to either isolated marginal.  The file proves:

```text
exactMediatedR2Dimension_n_ZFC_finite
exactProperMediatedR2Dimension_n_ZFC_finite
exactMediatedR2Dimension_n_ZFC_replacement_finite
exactProperMediatedR2Dimension_n_ZFC_replacement_finite
exactMediatedR2Dimension_n_ZFC_all
exactProperMediatedR2Dimension_n_ZFC_all
jointMediator_inaccessible_to_isolatedMarginals_ZFC_finite
jointMediator_inaccessible_to_isolatedMarginals_ZFC_replacement_finite
jointMediator_inaccessible_to_isolatedMarginals_ZFC_all
```

So the ZFC section gives exact mediated R2 dimension `n`, and also exact
proper mediated R2 dimension `n`, on carriers that still contain the
syntax-level ZFC axiom presentation.  It also names the isolated-marginal
obstruction directly: the joint mediator is inaccessible from the family-only
reader and from the role-only reader taken separately.

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

GodelR1R2Bridge.lean
  Proof/truth bridge: local Gödel-style data produces an R1/R2 residual and a
  two-state exact proper mediated dimension-2 gap.

ZornR1R2.lean
  Zorn's conclusion as local R1/R2 closure, plus dynamic trajectory
  preservation and a finite witness that terminal-only forgetting loses
  trajectory information.

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
