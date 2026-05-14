# R1R2proof

Self-contained Lean 4 development for the R1/R2 residual-mediation
framework, with a formula-level Peano arithmetic instance.

The project does not import mathlib.  It is intended to be auditable as a
small standalone Lake project.

## Main Result

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

The proved structural theorem is:

```text
The R1 trace projection sees PA axiom/component families and parameters.
It does not see the R2 base/step coordinate.
That coordinate appears as a diagonal residual.
A Fin 2 mediator separates the residual.
The exact proper mediated R2 dimension is 2.
```

This is a syntactic theorem about PA formulas and PA formula components.  It is
not a claim that PA is semantically false, and it is not a complete
formalization of first-order proof theory or model theory.

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

PeanoPAFormulaAxioms.lean
  Static formula-level PA instance and exact dimension-2 certificates.

PeanoPAFormulaAxiomsDynamic.lean
  Dynamic and temporal formula-level PA instance.

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

The repository does not yet contain:

```text
a full formalized proof system for first-order logic
a model theory of PA
a formula-level ZFC or enriched set-theory instance
an empirical world-model implementation
```

Those are natural extension targets, but they are not claimed by the current
Lean development.
