# Foundational Questions

Status: public orientation note.

The following questions mark the intended reading boundary between R1 and R2:

```text
Is Peano arithmetic in R1 or R2?

Is enriched set theory in R1 or R2?
```

In the terminology of `RegimesSelfContained.lean`, these questions ask whether
the corresponding formal systems merely certify internal coherence of an
explicit presentation, or whether they also provide certified local closure of
the required distinctions through the R2 residual and mediator structure.

## Current PA Status

For Peano arithmetic, the current formal answer is no longer just a question.
The files

```text
PeanoPAFormulaAxioms.lean
PeanoPAFormulaAxiomsDynamic.lean
```

formalize PA as syntax of first-order formulas:

```text
0, S, +, *
equality, negation, implication, conjunction, universal quantification
six standard PA axiom formulas
the induction schema
```

The proved structural result is:

```text
The R1 trace projection sees PA axiom/component families and parameters.
It does not see the R2 base/step coordinate.
That coordinate appears as a diagonal residual.
A Fin 2 mediator separates the residual.
The exact proper mediated R2 dimension is 2.
```

Thus, for the formula-level PA instance currently in the repository:

```text
PA under the trace projection is an R1 presentation that does not itself
access the R2 base/step coordinate.

The R2 coordinate is supplied by a certified minimal mediator.
```

This is a syntactic theorem about PA formulas and components.  It is not a
claim that PA is semantically false, nor a complete metatheory of first-order
logic.

## Current Set-Theory Status

The repository now contains the first syntax-level ZFC axiom file:

```text
ZFCFormulaAxioms.lean
```

It formalizes the pure first-order language of set theory and the standard ZFC
axiom formulas, including Separation, Replacement, and Choice, as syntax
objects.

The same file now contains a ZFC R1/R2 certificate section.  It operates on
formula-bearing ZFC objects, not on bare labels:

```text
ZFCFormulaAxiom
ZFCFormulaComponent
ZFCAllAxiomFiniteState n
```

For every `n >= 2`, the file gives finite exact-dimension certificates from
actual Separation formula components and actual Replacement formula components.
The full carrier includes every certified ZFC axiom object and both finite
schema-component families.  The finite schema-component formulas are determined
by their constructors and coordinates; they are not arbitrary formula/label
pairs.  Full ZFC axiom objects are embedded as certified formulas, without
arbitrary finite labels.  The R1 interface uses separate family and
component-role readers, so family-only and role-only marginal subfamilies are
tested explicitly by non-descent theorems.  The theorem

```text
exactMediatedR2Dimension_n_ZFC_all
exactProperMediatedR2Dimension_n_ZFC_all
```

proves exact mediated R2 dimension `n`, and also exact proper mediated R2
dimension `n`.

This is a syntactic structural certificate about ZFC formula objects.  It is
not a semantic theorem about models of ZFC or a proof-theoretic metatheorem.
