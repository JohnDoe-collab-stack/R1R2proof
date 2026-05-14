# Roadmap for Showing That R2 Goes Beyond Classical Mathematics

This note describes what must be done to justify the external claim that the
R2 regime goes beyond classical mathematics.

The current Lean file already proves the abstract R1/R2 architecture.  The
next step is not to change that abstract proof, but to instantiate it on a
standard classical formal system such as Peano arithmetic or ZFC.

## 1. Fix the Meaning of "Classical Mathematics"

The public claim must first define the comparison target.

In this project, classical mathematics should be represented as an R1 regime:

```lean
Coherent_R1 ...
```

R1 means that the system has an explicit presentation and an internal
coherence condition.  It can certify that its own presentation is coherent, but
it does not automatically certify that every required diagonal distinction is
closed.

The intended comparison is therefore:

> Classical mathematics, represented by PA or ZFC, is treated as an R1 regime.

This identification must be stated as an explicit hypothesis or proved by a
concrete formal instance.

## 2. Instantiate the R1 Regime on PA First

Peano arithmetic is the clean first target because its syntax, proof predicate,
substitution operation, and diagonal lemma are the classical setting of
Godel-style diagonalization.

The PA instance should provide:

```lean
PA_SyntaxConfiguration
PA_Interface
PA_activeInterfaces
PA_observationMap
PA_formalTarget
PA_R1_coherence
```

The active R1 interfaces should include only the classical data that the system
is allowed to read: formula codes, substitution data, proof data, and the
shared diagonal trace.

The phase or mediator information must not already be readable by the active
R1 interfaces.  Otherwise the R2 distinction would collapse back into R1.

## 3. Use Godelian Diagonalization to Produce the Residual

The core external bridge is a formal diagonalization construction.

The PA or ZFC library must supply, or allow us to build:

- coding of formulas;
- coding of proofs;
- substitution on codes;
- a proof predicate;
- a diagonal or fixed-point lemma;
- a canonical self-application configuration.

From this material, one must exhibit two configurations `x` and `y` such that:

```lean
JointSame obs I x y
```

but also:

```lean
RequiredDistinction sigma x y
```

Together, these give:

```lean
DiagonalizationWitness obs sigma I x y
```

and therefore:

```lean
ResidualNonempty_R2 obs sigma I
```

This is the formal point where R1 leaves a residual distinction unresolved.

## 4. Build the R2 Mediator

The R2 step is to introduce a mediator that reads the missing distinction.

For a two-phase diagonal construction, the natural mediator has type:

```lean
M : X -> Fin 2
```

It must separate every formal residual witness:

```lean
∀ x y, DiagonalizationWitness obs sigma I x y -> M x ≠ M y
```

This proves:

```lean
MediatedResidualEmpty obs sigma I M
```

So the diagonal residual left open by R1 is closed by R2.

## 5. Prove Irreducibility Back to R1

This is the decisive step for the claim that R2 goes beyond R1.

One must prove:

```lean
IrreducibleMediator obs I M
```

or, better:

```lean
WitnessedIrreducibleMediator obs I M
```

This says that the mediator does not descend to any proper active R1
subfamily.  In other words, R2 is not merely R1 with a renamed observation.

The stronger public statement depends on this step:

> R2 adds a residual-closure capacity that is not reducible to the active R1
> interfaces.

## 6. Prove Minimality if Possible

The strongest certificate is not only closure, but exact dimension.

The target theorem should have the form:

```lean
ExactProperMediatedR2Dimension obs sigma I 2
```

or equivalently an explicit dimension-minimal certificate:

```lean
DimensionMinimalProperMediatedR2Certificate obs sigma I M
```

This shows that the mediator is not an arbitrary addition.  It is the minimal
finite object needed to close the residual.

## 7. Repeat for ZFC Only After PA

ZFC should come after PA.

The ZFC version has the same logical shape, but a heavier formal environment:

- coding syntax inside set theory;
- coding proofs;
- formal satisfaction or provability machinery;
- diagonalization/fixed-point construction;
- extraction of the R1 interfaces;
- construction of the R2 mediator;
- irreducibility and minimality.

The PA version is the best first public bridge because it is smaller and closer
to the historical diagonal theorem.

## 8. Exact Claim Allowed After the PA Instance

Once the PA instance is complete, the precise claim is:

> Peano arithmetic, represented as an R1 regime, has a diagonal residual that
> is not closed by its active R1 interfaces.  The R2 mediator closes this
> residual and is irreducible to those R1 interfaces.  Therefore R2 is a
> strictly stronger regime of certification than R1 for this classical system.

If classical mathematics is represented by PA or by a stronger system such as
ZFC in the same R1 sense, then the broader conclusion becomes:

> R2 goes beyond classical mathematics not by adding more ordinary theorems,
> but by adding a new certified regime of residual closure.

## 9. What Must Not Be Overclaimed

The abstract Lean file already proves the R1/R2 machinery.  It does not, by
itself, formalize PA or ZFC.

Therefore the public presentation must keep these layers separate:

- the current repository proves the abstract R1/R2 theorem;
- a PA or ZFC instance proves that the theorem applies to a classical system;
- only after that instance can one state the external comparison with classical
  mathematics as a formal result rather than as an interpretation.

## 10. Recommended Implementation Order

1. Keep `RegimesSelfContained.lean` unchanged as the abstract certificate.
2. Add a separate PA candidate file.
3. Import the abstract certificate.
4. Define the PA syntax configurations and active interfaces.
5. Prove the canonical diagonal witness.
6. Define the phase mediator.
7. Prove mediated residual emptiness.
8. Prove irreducibility of the mediator.
9. Prove exact dimension `2` if the construction supports it.
10. Add a public note explaining that this is a residual-closure proof, not a
    conventional extension by extra axioms.

