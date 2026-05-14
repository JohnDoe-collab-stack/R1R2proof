# R1/R2 Notation

This note fixes the notation used to read the R1/R2 framework as a calculus of
relative identities.

The central point is that the framework does not start from equality of states.
It starts from indistinguishability relative to an observation regime.

## Observational Identity

Fix:

```text
S      : type of states
J      : type of interfaces
V      : type of observations
obs    : J -> S -> V
I      : Subfamily J
```

The Lean definition is:

```lean
JointSame obs I x y :=
  forall j : J, I j -> obs j x = obs j y
```

We write:

```text
x ≡ᵢ y
```

for:

```text
JointSame obs I x y
```

Reading:

```text
x and y have the same observational identity relative to the active interface
family I.
```

This is not Lean equality:

```text
x = y
```

It is a relative identity induced by the observations available through `I`.

## Required Distinction

Fix a target map:

```text
sigma : S -> Y
```

The Lean definition is:

```lean
RequiredDistinction sigma x y :=
  sigma x != sigma y
```

The target `sigma` asks for a distinction that the observation regime may or
may not preserve.

The basic R2 tension is:

```text
x ≡ᵢ y
but
sigma x != sigma y
```

In words:

```text
R1 identifies x and y observationally, while R2 requires them to be
distinguished.
```

## Diagonal Witness

The Lean definition is:

```lean
DiagonalizationWitness obs sigma I x y :=
  RequiredDistinction sigma x y
  and JointSame obs I x y
```

Using the notation:

```text
Diag_sigma,I(x,y) :=
  sigma x != sigma y
  and x ≡ᵢ y
```

A diagonal witness is therefore a fracture of relative identity:

```text
x and y are the same for the R1 observation regime,
but different for the R2 target.
```

Equivalently, the target `sigma` does not descend to the observational quotient
associated with `x ≡ᵢ y`.

The Lean development does not construct this quotient as an object.  The
quotient language is a reading of the obstruction:

```text
two states identified by the observation relation receive different sigma
values.
```

## Mediated Identity

Fix a finite mediator:

```text
M : S -> Fin n
```

The Lean definition is:

```lean
MediatedSame obs I M x y :=
  JointSame obs I x y
  and M x = M y
```

We write:

```text
x ≡ᵢ,ₘ y
```

for:

```text
JointSame obs I x y and M x = M y
```

Reading:

```text
x and y have the same observational identity relative to I, and the same
mediator coordinate M.
```

Thus `M` is not merely an extra label.  It is a finite refinement of the
observational identity relation.

## Mediated Residual

The Lean definition is:

```lean
MediatedResidual obs sigma I M x y :=
  RequiredDistinction sigma x y
  and MediatedSame obs I M x y
```

Using the notation:

```text
MedRes_sigma,I,M(x,y) :=
  sigma x != sigma y
  and x ≡ᵢ,ₘ y
```

The mediated residual contains the distinctions still lost after adding the
mediator coordinate.

Mediated closure says:

```text
there is no pair x,y such that
sigma x != sigma y
and x ≡ᵢ,ₘ y.
```

Equivalently:

```text
every diagonal witness for x ≡ᵢ y is separated by M.
```

## Minimal Refinement

When a mediator has type:

```text
M : S -> Fin n
```

the number `n` measures the size of the finite identity refinement.

An exact proper mediated R2 dimension:

```text
ExactProperMediatedR2Dimension obs sigma I n
```

means:

```text
there exists a proper mediated R2 certificate at dimension n,
and no such proper certificate exists at any smaller dimension.
```

In the Peano formula-level instance:

```text
n = 2
```

This means:

```text
Fin 2 is the smallest finite refinement of the R1 observational identity able
to separate the required R2 base/step distinction.
```

## Irreducibility

The mediator descent predicate says:

```lean
MediatorDescendsSubfamily obs K M :=
  forall x y, JointSame obs K x y -> M x = M y
```

In quotient language:

```text
M descends to the observational identity induced by K.
```

Witnessed irreducibility says that for every proper active subfamily `K`:

```text
there exist x,y such that
x ≡ₖ y
but
M x != M y.
```

Thus no strictly poorer observation regime carries the mediator coordinate.

The mediator is irreducible as a refinement of identity.

## Summary

The notation records the conceptual hierarchy:

```text
x = y
  Lean equality

x ≡ᵢ y
  observational identity relative to I

sigma x != sigma y
  required R2 distinction

x ≡ᵢ,ₘ y
  mediated observational identity
```

The core R1/R2 pattern is:

```text
R1 gives an observational identity.
R2 exposes a distinction not preserved by that identity.
A finite mediator refines the identity.
Exact dimension measures the minimal size of that refinement.
```

In the PA formula-level instance:

```text
R1 trace:
  PA formula families and parameters

R2 distinction:
  base/step coordinate

mediator:
  Fin 2 phase coordinate

meaning:
  the smallest finite repair of the R1 observational identity has dimension 2.
```
