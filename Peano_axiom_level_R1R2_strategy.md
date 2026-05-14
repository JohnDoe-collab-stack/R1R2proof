# Peano Axiom-Level R1/R2 Strategy

This note states the direct strategy.

The object is not a model of Peano arithmetic, and not a semantic truth
predicate.

The object is the Peano axioms themselves, taken as formal axioms.

The R1/R2 framework operates directly on these axioms as formal objects.

## 1. Peano Axioms as the Object

Use the usual first-order Peano signature:

```text
0
S
+
*
```

The basic Peano axioms are:

```text
forall x, S(x) != 0
```

```text
forall x y, S(x) = S(y) -> x = y
```

```text
forall x, x + 0 = x
```

```text
forall x y, x + S(y) = S(x + y)
```

```text
forall x, x * 0 = 0
```

```text
forall x y, x * S(y) = (x * y) + x
```

and the induction scheme, for every formula `phi(x)`:

```text
(phi(0) and forall x, (phi(x) -> phi(S(x)))) -> forall x, phi(x)
```

At the general axiom level, this can be represented as:

```lean
inductive PeanoAxiom
  | succ_ne_zero
  | succ_injective
  | add_zero
  | add_succ
  | mul_zero
  | mul_succ
  | induction (phi : Formula1)
```

This expresses the full Peano axiom family.  However, for the first Lean target,
this is not the cleanest substrate: `induction phi` is one global axiom.  Its
base and step premises are internal components of that axiom, not two separate
elements of `S`.

The first direct substrate should therefore be the finite recursive fragment:

```lean
inductive PARecAxiom
  | add_zero
  | add_succ
  | mul_zero
  | mul_succ
```

The first domain of operation is:

```lean
S := PARecAxiom
```

This still operates directly on true Peano axioms: the four constructors are
the addition and multiplication recursion axioms of Peano arithmetic.

The later induction-aware substrate can be:

```lean
inductive PeanoAxiomComponent
  | add_base
  | add_step
  | mul_base
  | mul_step
  | induction_base (phi : Formula1)
  | induction_step (phi : Formula1)
```

This second substrate separates the base and step components of induction.

The important point is that the substrate remains the Peano axioms themselves,
or their explicit axiom components.

## 2. Existing R1/R2 Machinery

The existing abstract certificate already has the required shape:

```lean
obs : J -> S -> V
I : J -> Prop
sigma : S -> Y
M : S -> Fin 2
```

So no new regime is needed.

The first instantiation uses:

```lean
S := PARecAxiom
```

## 3. Direct Axiom-Level R1

R1 consists of marginal readings of the Peano axioms.

Examples:

```text
which recursive family is this axiom in?
which operation symbol is involved?
is this part of the successor structure?
is this part of the addition structure?
is this part of the multiplication structure?
is this part of the induction scheme?
what common recursion trace does it belong to?
```

For the finite recursive fragment:

```lean
obs : J -> PARecAxiom -> V
```

and:

```lean
I : J -> Prop
```

selects the active marginal readings.

These readings are not the total text of the axiom.  If R1 reads the complete
axiom text, then the residual disappears, because the complete text already
distinguishes every axiom.

The relevant R1 level is therefore:

```text
marginal structural readings of the axioms
```

not:

```text
total syntactic identity of each axiom
```

## 4. The Peano Base/Step Axis

The Peano recursive axioms already contain a base/step structure.

For addition:

```text
add_zero : forall x, x + 0 = x
add_succ : forall x y, x + S(y) = S(x + y)
```

For multiplication:

```text
mul_zero : forall x, x * 0 = 0
mul_succ : forall x y, x * S(y) = (x * y) + x
```

For induction:

```text
base premise : phi(0)
step premise : forall x, phi(x) -> phi(S(x))
```

Thus the axioms themselves exhibit the finite distinction:

```text
base / step
```

## 5. R2 Target

The target reads this base/step distinction:

```lean
inductive Phase
  | base
  | step
```

For the recursive Peano axiom pairs:

```lean
sigma add_zero = Phase.base
sigma add_succ = Phase.step
sigma mul_zero = Phase.base
sigma mul_succ = Phase.step
```

The same idea applies to the induction axiom by reading its internal base and
step components.

The residual form is:

```lean
JointSame obs I x y
sigma x != sigma y
```

Example:

```text
x = add_zero
y = add_succ
```

They can share the same R1 recursion-family reading:

```text
addition recursion
```

while differing on:

```text
base / step
```

## 6. R2 Mediator

The mediator is the finite base/step readout:

```lean
M : PARecAxiom -> Fin 2
```

with:

```lean
M add_zero = 0
M add_succ = 1
M mul_zero = 0
M mul_succ = 1
```

It closes the residual when:

```lean
forall x y,
  DiagonalizationWitness obs sigma I x y ->
    M x != M y
```

This gives:

```lean
MediatedResidualEmpty obs sigma I M
```

## 7. Irreducibility

For the first Lean target, the active interface family has one interface:

```lean
PARecInterface.recursionFamily
```

A proper active subfamily removes this reading.  On such a subfamily,
`add_zero` and `add_succ` remain indistinguishable, while the mediator still
separates them:

```lean
M add_zero != M add_succ
```

Thus the mediator does not descend to any proper active subfamily:

```lean
IrreducibleMediator obs_PA_axiom I_PA_axiom M_PA_axiom
```

Equivalently:

```lean
forall K,
  Subfamily.Proper K I_PA_axiom ->
    not (MediatorDescendsSubfamily obs_PA_axiom K M_PA_axiom)
```

The correct statement is non-descent:

```text
M_PA_axiom does not descend to a proper subfamily.
```

not:

```text
M_PA_axiom descends with contradiction.
```

## 8. Exact Statement

The direct axiom-level claim is:

```text
R1 reads marginal structural projections of the true recursive Peano axioms.
R2 reads the finite base/step coordinate already present in those axioms.
The R2 mediator closes a residual distinction that the chosen R1 readings do
not close.
```

This is not the claim that Peano axioms are assumed as Lean axioms.

It is the claim that the R1/R2 certificate operates directly on Peano axiom
objects or explicit Peano axiom components.

## 9. Minimal Lean Target

A first Lean file should not start by formalizing all of Peano arithmetic.

It should first instantiate the existing R1/R2 framework on the finite recursive
Peano axiom fragment:

```lean
PARecAxiom
PARecInterface
obs_PA_axiom
I_PA_axiom
sigma_PA_axiom
M_PA_axiom
```

and prove:

```lean
existsCanonicalDiagonalWitness_PA_axiom
mediatedResidualEmpty_M_PA_axiom
irreducibleMediator_M_PA_axiom
properMediatedR2Certificate_M_PA_axiom
exactProperMediatedR2Dimension_two_PA_axiom
```

This proves the complete certificate on true Peano recursion axioms:

```text
R1 reads recursion family.
R2 reads base/step phase.
add_zero and add_succ give the canonical residual witness.
M : PARecAxiom -> Fin 2 closes the residual.
The proper mediated R2 dimension is exactly 2.
```

## 10. Induction Extension

After the finite recursive fragment, the induction scheme should be handled by
moving from whole axioms to axiom components:

```lean
S := PeanoAxiomComponent
```

The induction instance:

```text
(phi(0) and forall x, (phi(x) -> phi(S(x)))) -> forall x, phi(x)
```

then contributes:

```lean
PeanoAxiomComponent.induction_base phi
PeanoAxiomComponent.induction_step phi
```

This keeps the same R1/R2 structure:

```text
R1 reads the induction family and formula parameter.
R2 reads base/step.
```
