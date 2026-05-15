# ZFC Formula-Axiom Specification

Status: implemented target specification.

This document fixes the requirements implemented by `ZFCFormulaAxioms.lean`.
The file formalizes ZFC at the same syntax level of rigor as the Peano
formula-level instance.

The target is not a label-level encoding.  The target is a syntax-level
encoding of the standard first-order axioms of ZFC as actual `Formula` trees.

## Non-Negotiable Requirements

The ZFC development satisfies the following requirements.

```text
No labels-only encoding.
No ZFC-like placeholder.
No omission of Choice when the file is called ZFC.
No semantic model theory claim.
No imported axioms standing for ZFC truth.
No quotient.
No Classical.
No propext.
```

The objects of study must be syntactic formulas.

The object type is:

```lean
structure ZFCFormulaAxiom where
  formula : Formula
  witness : IsZFCFormulaAxiom formula
```

The witness certifies that the formula is one of the standard ZFC axioms or an
instance of one of the standard ZFC axiom schemas.

## First-Order Language

The underlying language is the pure first-order language of set theory.

There are no function symbols and no constant symbols in the primitive
language.

Terms are variables:

```lean
inductive Term
  | var : Nat -> Term
```

Formulas must include at least:

```lean
inductive Formula
  | falsum : Formula
  | equal : Term -> Term -> Formula
  | mem : Term -> Term -> Formula
  | not : Formula -> Formula
  | and : Formula -> Formula -> Formula
  | or : Formula -> Formula -> Formula
  | imp : Formula -> Formula -> Formula
  | iff : Formula -> Formula -> Formula
  | forallE : Nat -> Formula -> Formula
  | existsE : Nat -> Formula -> Formula
```

The implementation may later define derived notation such as:

```text
x != y
x ∉ y
∃! x, P x
subset x y
empty x
```

but the axiom objects themselves must expand to explicit `Formula` syntax.

## Variable Discipline

The first Lean target uses natural-number variable names with explicit binder
indices, as the PA file currently does.

For the schema axioms, the specification must track the relevant variable
roles explicitly:

```text
ambient set variable
subset/image set variable
element variable
parameter variables
formula parameter phi
```

The implementation must state clearly which variable indices are reserved by
each axiom constructor.

The final ZFC formula-axiom target must not hide variable conditions.  It must
either implement enough free-variable and substitution discipline to enforce
the schema side conditions, or store the required freshness/variable-role
conditions explicitly as data in the schema constructors.

This is a single-file target.  The file may contain separate sections for
syntax, derived predicates, axiom formulas, components, and R1/R2
certificates, but the intended implementation is one Lean file rather than a
multi-file decomposition.

## Standard ZFC Axioms To Encode

The file must encode the following standard ZFC axioms exhaustively.

### 1. Extensionality

```text
forall x y,
  (forall z, z ∈ x <-> z ∈ y) -> x = y
```

### 2. Empty Set

```text
exists x,
  forall z, z ∉ x
```

Even if empty set can be derived from other presentations, this file must
include it explicitly when using the exhaustive standard list.

### 3. Pairing

```text
forall a b,
  exists p,
    forall z, z ∈ p <-> (z = a or z = b)
```

### 4. Union

```text
forall x,
  exists u,
    forall z, z ∈ u <-> exists y, z ∈ y and y ∈ x
```

### 5. Power Set

```text
forall x,
  exists p,
    forall z, z ∈ p <-> z ⊆ x
```

where:

```text
z ⊆ x := forall w, w ∈ z -> w ∈ x
```

### 6. Infinity

The file must choose and document one standard von Neumann-style formulation.

Recommended formulation:

```text
exists x,
  empty ∈ x
  and
  forall y, y ∈ x -> successor(y) ∈ x
```

with derived syntactic definitions:

```text
empty(e) := forall z, z ∉ e
successor(y, s) := forall z, z ∈ s <-> (z ∈ y or z = y)
```

Expanded version:

```text
exists x,
  (exists e, empty(e) and e ∈ x)
  and
  forall y,
    y ∈ x ->
      exists s, successor(y, s) and s ∈ x
```

This avoids treating `empty` or `successor` as primitive terms.

### 7. Separation Schema

For every formula `phi`, ZFC contains the separation instance:

```text
forall a,
  exists b,
    forall x,
      x ∈ b <-> (x ∈ a and phi(x, parameters))
```

The Lean constructor should have the shape:

```lean
| separation (phi : Formula) (data : SeparationData) :
    IsZFCFormulaAxiom (zfcSeparationFormula phi data)
```

`SeparationData` must record the variable indices for:

```text
a : source set
b : subset set
x : element
parameters
```

The file must enforce or explicitly store the side condition that `b` is not
captured by `phi`.  A final ZFC axiom file must not leave this condition as an
informal comment only.

Recommended shape:

```lean
structure SeparationSideConditions where
  b_not_free_in_phi : Prop
  bound_vars_fresh : Prop
  role_vars_distinct : Prop

structure SeparationData where
  a : Nat
  b : Nat
  x : Nat
  params : List Nat
  side : SeparationSideConditions
```

### 8. Replacement Schema

For every formula `phi`, ZFC contains the replacement instance:

```text
forall a,
  (forall x, x ∈ a -> exists unique y, phi(x, y, parameters))
  ->
  exists b,
    forall y,
      y ∈ b <-> exists x, x ∈ a and phi(x, y, parameters)
```

The Lean constructor should have the shape:

```lean
| replacement (phi : Formula) (data : ReplacementData) :
    IsZFCFormulaAxiom (zfcReplacementFormula phi data)
```

`ReplacementData` must record the variable indices for:

```text
a : source set
b : image set
x : source element
y : image element
parameters
```

It must also enforce or explicitly store the freshness conditions needed for
the image variable and bound variables used by the schema instance.

Recommended shape:

```lean
structure ReplacementSideConditions where
  b_not_free_in_phi : Prop
  image_vars_fresh : Prop
  bound_vars_fresh : Prop
  role_vars_distinct : Prop

structure ReplacementData where
  a : Nat
  b : Nat
  x : Nat
  y : Nat
  params : List Nat
  side : ReplacementSideConditions
```

The uniqueness predicate must be expanded syntactically, for example:

```text
exists y,
  phi(x, y)
  and
  forall y',
    phi(x, y') -> y' = y
```

### 9. Foundation / Regularity

```text
forall x,
  x != empty ->
    exists y,
      y ∈ x and forall z, z ∈ y -> z ∉ x
```

Since there is no primitive empty-set constant, use the expanded empty
predicate:

```text
x != empty
```

as:

```text
exists z, z ∈ x
```

So the recommended formula is:

```text
forall x,
  (exists z, z ∈ x) ->
    exists y,
      y ∈ x and forall z, z ∈ y -> z ∉ x
```

### 10. Choice

Because the target is ZFC and not ZF, Choice is mandatory.

The file must choose one standard first-order formulation and keep it fixed.

Recommended formulation:

```text
Every set of nonempty pairwise disjoint sets has a choice set.
```

Expanded:

```text
forall x,
  (
    (forall y, y ∈ x -> exists z, z ∈ y)
    and
    (forall y z,
      y ∈ x -> z ∈ x -> y != z ->
        not exists w, w ∈ y and w ∈ z)
  )
  ->
  exists c,
    (forall u, u ∈ c -> exists y, y ∈ x and u ∈ y)
    and
    forall y,
      y ∈ x ->
        exists u,
          u ∈ y
          and u ∈ c
          and forall v, (v ∈ y and v ∈ c) -> v = u
```

This formulation avoids introducing a primitive function symbol and also
requires the choice set to live inside the union of the family.

If a different standard form is chosen, such as the well-ordering theorem, the
file must state that choice explicitly and encode that formula syntactically.

## Implemented Lean Structure

The Lean file is organized around the following definitions:

```lean
namespace LocalSemanticClosure
namespace ZFCFormulaAxioms

inductive Term
inductive Formula

def neq ...
def notMem ...
def subset ...
def emptyPred ...
def successorPred ...
def existsUnique ...

structure SeparationSideConditions where ...
structure SeparationData where ...
structure ReplacementSideConditions where ...
structure ReplacementData where ...

inductive AxiomFamily
inductive ZFCSchemaRole
inductive ZFCComponentRole

def zfcExtensionalityFormula : Formula := ...
def zfcEmptySetFormula : Formula := ...
def zfcPairingFormula : Formula := ...
def zfcUnionFormula : Formula := ...
def zfcPowerSetFormula : Formula := ...
def zfcInfinityFormula : Formula := ...
def zfcSeparationFormula (phi : Formula) (data : SeparationData) : Formula := ...
def zfcReplacementFormula (phi : Formula) (data : ReplacementData) : Formula := ...
def zfcFoundationFormula : Formula := ...
def zfcChoiceFormula : Formula := ...

inductive IsZFCFormulaAxiom : Formula -> Type
  | extensionality : IsZFCFormulaAxiom zfcExtensionalityFormula
  | empty_set : IsZFCFormulaAxiom zfcEmptySetFormula
  | pairing : IsZFCFormulaAxiom zfcPairingFormula
  | union : IsZFCFormulaAxiom zfcUnionFormula
  | power_set : IsZFCFormulaAxiom zfcPowerSetFormula
  | infinity : IsZFCFormulaAxiom zfcInfinityFormula
  | separation (phi : Formula) (data : SeparationData) :
      IsZFCFormulaAxiom (zfcSeparationFormula phi data)
  | replacement (phi : Formula) (data : ReplacementData) :
      IsZFCFormulaAxiom (zfcReplacementFormula phi data)
  | foundation : IsZFCFormulaAxiom zfcFoundationFormula
  | choice : IsZFCFormulaAxiom zfcChoiceFormula

structure ZFCFormulaAxiom where
  formula : Formula
  witness : IsZFCFormulaAxiom formula

structure ZFCFormulaComponent where
  formula : Formula
  family : AxiomFamily
  role : ZFCComponentRole

inductive ZFCAllAxiomFiniteState (n : Nat)
  | axiom : Fin n -> ZFCFormulaAxiom -> ZFCAllAxiomFiniteState n
  | parameterComponent : Fin n -> ZFCAllAxiomFiniteState n

end ZFCFormulaAxioms
end LocalSemanticClosure
```

The component type is required in the same file if the R1/R2 certificate is
implemented there.  It must still carry actual `Formula` objects; it must not
replace formulas with component labels.

## R1/R2 Section After Syntax

The R1/R2 section is added only after the syntax-level ZFC axioms are present
in the same file.

The R1/R2 layer must not replace the axiom formulas.  It must operate on
objects carrying those formulas.

Implemented state types:

```lean
ZFCFormulaAxiom
ZFCFormulaComponent
ZFCAllAxiomFiniteState n
```

Implemented R1 observations include:

```text
component trace
axiom family
component role
```

Implemented R2 targets include:

```text
finite coordinate Fin n
```

The dimension must be justified by a real syntactic structure in ZFC.  It must
not be obtained by adding artificial labels.

## Acceptance Criteria

A first acceptable single ZFC Lean file must satisfy:

```text
1. It compiles as part of the Lake project.
2. It imports no mathlib.
3. It defines the pure first-order set-theory language.
4. It defines each listed ZFC axiom as a Formula tree.
5. It includes Separation and Replacement as schema constructors.
6. It includes Choice.
7. It defines ZFCFormulaAxiom as formula plus witness.
8. If it defines components, every component still carries an actual Formula.
9. It contains an AXIOM_AUDIT block.
10. The audit prints no dependency on Classical, propext, or arbitrary axioms.
11. The README states exactly what is and is not formalized.
```

The R1/R2 ZFC certificate section also satisfies:

```text
1. It operates on ZFCFormulaAxiom or ZFCFormulaComponent objects.
2. It identifies an explicit R1 projection.
3. It identifies an explicit R2 target.
4. It gives a concrete diagonal residual witness.
5. It gives a concrete mediator.
6. It proves mediated residual closure.
7. It proves irreducibility or witnessed irreducibility when claimed.
8. It proves the exact mediated dimension when claimed.
9. It does not claim a semantic theorem about ZFC unless a separate model or
   proof theory has actually been formalized.
```

## Boundary Statement

This specification is about ZFC as syntax.

It does not by itself prove:

```text
consistency of ZFC
inconsistency of ZFC
truth of ZFC in a model
completeness or soundness of first-order logic
independence of Choice
Gödel incompleteness
```

Those would require additional formal layers.

The implemented milestone is stricter and narrower:

```text
ZFC axioms are present exhaustively as syntactic Formula objects, and R1/R2
certificates operate directly on formula-bearing ZFC objects.
```

The implemented theorem package includes, for every `n >= 2`:

```text
exactProperMediatedR2Dimension_n_ZFC_finite
exactProperMediatedR2Dimension_n_ZFC_all
endToEnd_ZFC_all
```
