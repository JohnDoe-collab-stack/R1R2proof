# R1 / R2: Explicit Presentation and Local Informational Faithfulness

This note fixes a technical distinction between two regimes.

```text
R1: explicit closure of a presentation.
R2: local closure of required distinctions by certified mediation.
```

The contrast is not about the richness of the system. It is about what is
certified.

```text
R1 certifies a property of the explicit presentation.
R2 certifies local preservation of required distinctions.
```

## 1. Common Framework

Fix:

```text
S      : type of local states;
Y      : type of target values;
J      : type of interfaces;
V      : type of observations;
sigma  : S -> Y;
obs    : J -> S -> V;
I      : subfamily of J.
```

The target signature `sigma` determines the required distinctions:

```text
Req_sigma(x,y) :=
  sigma x != sigma y.
```

The interface regime `I` determines local indistinguishability:

```text
Same_I(x,y) :=
  for every j in I, obs j x = obs j y.
```

The diagonal witness is:

```text
Diag_sigma,I(x,y) :=
  Req_sigma(x,y) and Same_I(x,y).
```

Reading:

```text
sigma separates x and y;
I does not separate them.
```

In Lean:

```text
Req_sigma    = RequiredDistinction sigma x y
Same_I       = JointSame obs I x y
Diag_sigma,I = DiagonalizationWitness obs sigma I x y
Residual     = Diag_sigma,I
```

The local residual is the class of diagonal witnesses still present:

```text
Res_sigma(I) :=
  { (x,y) | Diag_sigma,I(x,y) }.
```

Direct local closure is:

```text
Closed_sigma(I) :=
  for all x,y,
  Same_I(x,y) implies sigma x = sigma y.
```

Therefore:

```text
Closed_sigma(I) iff Res_sigma(I) = empty.
```

In an exhaustive finite presentation:

```text
rho_sigma(I) = # Res_sigma(I)
rho_sigma(I) = 0 iff Closed_sigma(I).
```

The scalar `rho` is therefore a counting coordinate. It is not the main object.
The main object is the diagonal witness.

## 2. The R1 Regime

The module `RegimesSelfContained.lean` isolates R1 in its minimal form as a
regime certifying an explicit presentation. This section gives only the reading
needed to compare R1 and R2.

### Definition of R1

R1 is the regime in which a presentation is controlled by its explicit objects:

```text
formulas;
rules;
derivations;
projections;
explicitly designated models;
contents accessible in the presentation.
```

An R1 criterion has the form:

```text
Coherent_R1(T) :=
  no internal obstruction to T is derivable or realized.
```

The standard case is:

```text
Coherent_R1(T) :=
  T does not derive bottom.
```

### Object Certified by R1

An R1 certificate concerns:

```text
T;
a derivation in T;
an absence of contradiction in T;
a projection pi defined in T;
an output compatible with the rules of T;
a model explicitly admitted for T.
```

An R1 certificate can therefore establish:

```text
pi(x) = expected decision;
T |- phi;
T does not derive bottom;
T has a model in a given class.
```

### Limit of R1

R1 does not contain, by itself, the following predicate:

```text
Diag_sigma,I(x,y).
```

It therefore does not ask:

```text
is the distinction required by sigma
still accessible from I?
```

A presentation may satisfy its R1 criterion and produce an output that is
correct relative to its projection while still leaving a required distinction
open:

```text
pi produces the right value;
but there exist x,y such that Diag_sigma,I(x,y).
```

In this case the output is compatible with the presentation, but preservation
of the required information is not certified.

### Enriched R1 Presentations

An explicit enrichment is not enough to leave R1.

The following remain R1 as long as they do not certify closure of diagonal
witnesses:

```text
memory;
history;
recall;
projection;
compression;
selection;
association table;
explicit dynamic procedure.
```

These mechanisms may increase computational power or output quality. They do
not change regime as long as their certificate remains:

```text
available content -> projection -> compatible output.
```

## 3. The R2 Regime

### Definition of R2

R2 is the regime in which the certificate concerns local closure of required
distinctions.

An R2 problem is given by:

```text
(S, J, obs, sigma, I)
```

with obstruction:

```text
Diag_sigma,I(x,y).
```

Local informational closure can be formulated as:

```text
Closed_R2(sigma,I) :=
  no unresolved diagonal witness remains.
```

There are two cases.

### Direct R2

Closure is direct when:

```text
Res_sigma(I) = empty.
```

Equivalent:

```text
Closed_sigma(I).
```

Equivalent, under an exhaustive finite presentation:

```text
rho_sigma(I) = 0.
```

### Mediated R2

The mediated case is the structurally characteristic case of the project.

We start from:

```text
Res_sigma(I) != empty.
```

Therefore there exist:

```text
x,y such that Diag_sigma,I(x,y).
```

An R2 mediation adds an object:

```text
M : S -> Fin n.
```

This mediator verifies:

```text
M makes the distinction readable;
M closes the witness;
M does not descend to proper subfamilies;
in the dimension-minimal version,
no mediator of strictly smaller dimension provides
a proper mediated R2 certificate.
```

Define:

```text
Same_{I,M}(x,y) :=
  Same_I(x,y) and M(x) = M(y).
```

The mediated residual is:

```text
Res_sigma(I,M) :=
  { (x,y) | Req_sigma(x,y) and Same_{I,M}(x,y) }.
```

Mediated closure requires:

```text
Res_sigma(I,M) = empty.
```

Equivalent:

```text
for every diagonal witness (x,y) of I,
M(x) != M(y).
```

The mediated R2 chain is:

```text
Req_sigma(x,y) and Same_I(x,y)
-> Diag_sigma,I(x,y)
-> positive Res_sigma(I)
-> obstruction to proper-subfamily descent
-> joint mediator M
-> non-descent of M
-> Res_sigma(I,M) = empty
-> certificate.
```

The complete mediated R2 certificate groups two obligations:

```text
MediatedR2Certificate(sigma,I,M) :=
  Res_sigma(I,M) = empty
  and M does not descend to proper subfamilies.
```

The proper mediated case adds that the residual was present before mediation:

```text
ProperMediatedR2Certificate(sigma,I,M) :=
  Res_sigma(I) != empty
  and Res_sigma(I,M) = empty
  and M does not descend to proper subfamilies.
```

The dimension-minimal version adds the exact size invariant:

```text
DimensionMinimalProperMediatedR2Certificate(sigma,I,M,n) :=
  ProperMediatedR2Certificate(sigma,I,M)
  and for every m < n,
      no proper mediated R2 certificate exists at dimension m.
```

The witness-strengthened version keeps non-descent in positive form:

```text
DimensionMinimalWitnessedProperMediatedR2Certificate(sigma,I,M,n) :=
  initial residual nonempty
  and Res_sigma(I,M) = empty
  and every proper subfamily has an explicit non-descent witness
  and no smaller dimension carries a proper certificate.
```

## 4. Formal Difference Between R1 and R2

R1 may certify:

```text
pi(x) = y.
```

R2 asks:

```text
pi(x) = y
because the required distinction supporting that decision
is preserved directly or separated by certified mediation.
```

The difference is not:

```text
less computation / more computation.
```

The difference is:

```text
extensional agreement / informational faithfulness.
```

R1 controls agreement of an output with a presentation.

R2 controls preservation of the distinction that makes that output determined
in the interface regime under consideration.

## 5. Incidence

The incidence layer gives the finite form of R2.

Fix a domain of distinctions `D`.

```text
Required(d) : d is required;
Loss(j,d)  : interface j loses d;
I          : family of interfaces.
```

The common residual is:

```text
CommonResidual(I,d) :=
  Required(d) and for every j in I, Loss(j,d).
```

Thus:

```text
Res(I) = intersection over j in I of L_j.
```

Closure by losses is:

```text
ClosedByLoss(I) :=
  no d satisfies CommonResidual(I,d).
```

Thus:

```text
ClosedByLoss(I) iff Res(I) = empty.
```

Irreducibility is:

```text
IrreducibleClosedByLoss(I) :=
  ClosedByLoss(I)
  and for every strict subfamily K < I,
      not ClosedByLoss(K).
```

In a finite presentation:

```text
rhoList = 0 iff ClosedByLoss(I).
```

Cardinalization comes after incidence:

```text
required distinctions
-> losses by interface
-> intersection of losses
-> residual witnesses
-> rho coordinate.
```

## 6. Minimal Joint Mediator

The minimal joint mediator is the characteristic object of R2.

Even when an R2 certificate is syntactically represented in an explicit
presentation, what it certifies remains different: it certifies closure of a
residual of distinctions, not merely internal compatibility of a derivation or
projection.

It establishes:

```text
the distinction is not separated by the marginals;
the mediator separates it;
the mediator cannot be recovered from a proper subfamily;
the diagonal witness is closed by this mediated separation.
```

Abstract form:

```text
IrreducibleMediator(obs,I,M) :=
  for every K < I,
  M does not descend to K.
```

In the standalone static R2 layer, dimension minimality is already expressed by:

```text
DimensionMinimalProperMediatedR2Certificate
DimensionMinimalWitnessedProperMediatedR2Certificate
```

It gives:

```text
1. presence of a residual before mediation;
2. closure of the residual by M : S -> Fin n;
3. non-descent, with a version strengthened by explicit witnesses;
4. absence of a proper certificate in every dimension m < n.
```

The name `FamilyIrreducibleMediationProfile` does not occur in the standalone
module. In this file, its static core is carried by:

```text
DimensionMinimalWitnessedProperMediatedR2Certificate
```

which packages mediated closure, non-descent to proper subfamilies, explicit
witnesses, and dimensional minimality.

This is not a quantitative improvement of R1. It is another kind of
certificate.

## 7. Classification Table

```text
R1
  Data:
    T, rules, derivations, projections, designated models.

  Obstruction:
    contradiction, internal incompatibility, projection failure.

  Criterion:
    the explicit presentation remains coherent or compatible.

  Certificate:
    proof internal to the presentation.

  What is not certified:
    accessibility of a required distinction through I.
```

```text
R2
  Data:
    sigma, I, obs, residual, mediator, certificate.

  Obstruction:
    Diag_sigma,I(x,y).

  Criterion:
    no unresolved diagonal witness remains.

  Certificate:
    direct closure or closure by irreducible joint mediator.

  What is certified:
    required distinctions are preserved
    or separated by certified local closure.
```

## 8. Compact Form

```text
R1:
  the explicit presentation holds.

R2:
  the required distinctions hold in the interface regime.
```

More precisely:

```text
R1:
  no internal obstruction to the explicit presentation.

R2:
  no unresolved diagonal witness relative to sigma and I.
```

The contribution of `LocalSemanticClosure` is to formalize R2:

```text
RequiredDistinction
-> JointSame
-> DiagonalizationWitness
-> Residual
-> incidence of losses
-> irreducible joint mediator
-> non-descent
-> certified closure.
```
