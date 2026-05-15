# Dynamic LLM R1/R2 Alignment Proof Plan

## Objective

The complete target is dynamic, not merely static.

The goal is to formalize a Lean instance showing that terminal or visible
alignment observations can leave a residual distinction between causal
trajectories across steps, and that closing this residual requires a finite
mediator of exact uniform dimension.

The target theorem is:

```text
For every n >= 2, there is a dynamic R1/R2 alignment carrier such that:

1. at each dynamic step, R1 observations identify n causal trajectories;
2. the R2 target distinguishes those trajectories;
3. a step-indexed mediator M step : S -> Fin n closes the residual;
4. every smaller mediator S -> Fin m with m < n fails at each step;
5. terminal-only and prompt-only marginal interfaces do not recover the
   mediator;
6. the dimension n is uniform across the dynamic steps.
```

The static certificate is only a local lemma at each step.  The proof aimed at
LLM alignment must start from the dynamic framework.

## Boundary

This Lean development would prove a structural theorem about an abstract
dynamic alignment model.

It would not by itself prove:

```text
real LLMs have exactly this carrier;
real transformer internals instantiate this model;
empirical ASLMT logs satisfy the Lean definitions;
alignment is solved for deployed systems.
```

Those four claims require an additional empirical/certification bridge after
the dynamic Lean theorem exists.

The document therefore separates four levels:

```text
Level 1: dynamic Lean theorem.
Level 2: transformer/LLM interpretation of the carrier.
Level 3: ASLMT certificate extraction from logs.
Level 4: deployed-system alignment claim.
```

Only Level 1 belongs in the first Lean file.

## Existing Dynamic R1/R2 Structure To Reuse

The new file should import the dynamic kernel:

```lean
import DynamicRegimesSelfContained
import FiniteDimensionHierarchy
```

The proof should use the namespace:

```lean
open Standalone.RegimesSelfContained
open Standalone.DynamicRegimesSelfContained
```

The dynamic definitions to reuse are:

```lean
DynamicTarget
DynamicDiagonalizationWitness
DynamicResidual_R2
DynamicResidualNonempty_R2
DynamicMediatedResidualEmpty
StepwiseProperMediatedR2Certificate
DynamicExactProperMediatedR2Dimension
UniformProperMediatedR2Certificate
FamilyIrreducibleDynamicMediationProfile
StepSeparatesFiber
CompatDimLe
CompatDimEq
FamilyIrreducibleCompatibilityProfile
endToEnd_familyIrreducibleCompatibilityProfile_subset
```

The static definitions are still used inside each step:

```lean
JointSame
RequiredDistinction
DiagonalizationWitness
ResidualNonempty_R2
MediatedResidualEmpty
MediatorDescendsSubfamily
WitnessedIrreducibleMediator
ProperMediatedR2Certificate
ExactProperMediatedR2Dimension
FiniteDimensionHierarchy.no_injective_fin_of_lt
```

No quotient, no `Classical`, no `propext`.

## File Name

Recommended Lean file:

```text
LLMAlignmentDynamicR1R2.lean
```

The root file must import it:

```lean
import LLMAlignmentDynamicR1R2
```

Recommended README section after compilation:

```text
Dynamic LLM/R1R2 Alignment Instance
```

## Core Interpretation

The carrier represents dynamic causal states.

```text
S      = complete causal trajectory states
Step   = dynamic context / evaluation step
R1     = visible prompt and terminal-output observation
R2     = step-relative causal trajectory coordinate
M step = step-indexed causal mediator
```

The formal reading:

```text
R1 says:
  two states are indistinguishable through visible prompt/terminal interfaces.

R2 says:
  at a given step, the states must still be distinguished because their causal
  trajectory coordinates differ.

M step says:
  this is the finite mediator that restores exactly the missing trajectory
  coordinate at that step.
```

## No Artificial Label Discipline

The carrier must not attach a free coordinate to an independent visible state.

Avoid:

```lean
structure BadAlignmentState (n : Nat) where
  terminalOutput : TerminalOutput
  coordinate : Fin n
```

The coordinate must be introduced by the causal trajectory constructor.

Minimal allowed pattern:

```lean
inductive AlignmentState (n : Nat)
  | trajectoryClass : Fin n -> AlignmentState n
```

Richer allowed pattern:

```lean
inductive AlignmentState (n : Nat)
  | trajectoryClass :
      (i : Fin n) ->
      PromptClassFor i ->
      TerminalOutputFor i ->
      DecisionTraceFor i ->
      AlignmentState n
```

Audit rule:

```text
M step must be recovered from the trajectory constructor.
It must not be a coordinate attached after terminal observations are chosen.
```

## Dynamic Types

The first complete file should keep the dynamic model finite and auditable.

Recommended minimal types:

```lean
inductive AlignmentStep
  | step : Nat -> AlignmentStep
deriving DecidableEq

inductive AlignmentState (n : Nat)
  | trajectoryClass : Fin n -> AlignmentState n

inductive TerminalOutput
  | sameVisibleOutput
deriving DecidableEq

inductive PromptClass
  | samePromptClass
deriving DecidableEq
```

The `Nat` inside `AlignmentStep` supplies a real step axis.  The complete
target should not leave this axis inert.  It should use a step-dependent
trajectory transform.

## Interfaces

The interface must be split into visible marginal readers.

```lean
inductive AlignmentInterface
  | terminalOutputReader
  | promptClassReader
deriving DecidableEq
```

The observation codomain should keep the two visible types separated:

```lean
inductive AlignmentObservation
  | terminalOutput : TerminalOutput -> AlignmentObservation
  | promptClass : PromptClass -> AlignmentObservation
deriving DecidableEq
```

Active family:

```lean
def I_alignment : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => True
  | AlignmentInterface.promptClassReader => True
```

Marginal subfamilies:

```lean
def I_alignment_terminal_only : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => True
  | AlignmentInterface.promptClassReader => False

def I_alignment_prompt_only : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => False
  | AlignmentInterface.promptClassReader => True
```

Required properness lemmas:

```lean
terminal_only_proper_alignment :
  Subfamily.Proper I_alignment_terminal_only I_alignment

prompt_only_proper_alignment :
  Subfamily.Proper I_alignment_prompt_only I_alignment
```

## R1 Observation

The R1 observation must not read the trajectory coordinate.

```lean
def obs_alignment {n : Nat} :
    AlignmentInterface -> AlignmentState n -> AlignmentObservation
  | AlignmentInterface.terminalOutputReader, _ =>
      AlignmentObservation.terminalOutput TerminalOutput.sameVisibleOutput
  | AlignmentInterface.promptClassReader, _ =>
      AlignmentObservation.promptClass PromptClass.samePromptClass
```

This encodes:

```text
all causal trajectories look identical to the visible R1 interface.
```

Required lemma:

```lean
jointSame_alignmentStates :
  ∀ i j : Fin n,
    JointSame obs_alignment I_alignment
      (AlignmentState.trajectoryClass i)
      (AlignmentState.trajectoryClass j)
```

## Step Transform

The dynamic target should vary with the step while preserving exact
dimension.

For `h : 1 < n`, define:

```lean
def firstTrajectory {n : Nat} (h : 1 < n) : Fin n := ...
def secondTrajectory {n : Nat} (h : 1 < n) : Fin n := ...
```

Then define a step transform:

```lean
def stepTransform {n : Nat} (h : 1 < n) :
    AlignmentStep -> Fin n -> Fin n
```

Recommended first nontrivial implementation:

```text
even steps: identity
odd steps: swap firstTrajectory h and secondTrajectory h, fix all other points
```

Required theorem:

```lean
stepTransform_injective :
  ∀ step : AlignmentStep,
    Function.Injective (stepTransform h step)
```

This is the exact point that makes the dynamic axis non-inert while preserving
the finite dimension lower bound.

## Dynamic R2 Target

The target must be dynamic:

```lean
def target_alignment {n : Nat} (h : 1 < n) :
    DynamicTarget (AlignmentState n) AlignmentStep (Fin n) :=
  { targetAt := fun step s =>
      match s with
      | AlignmentState.trajectoryClass i => stepTransform h step i }
```

The target is step-relative: the same trajectory class may be read through a
different finite coordinate at different steps.

## Step-Indexed Mediator

The mediator must be step-indexed:

```lean
def M_alignment {n : Nat} (h : 1 < n) :
    AlignmentStep -> AlignmentState n -> Fin n :=
  fun step s =>
    match s with
    | AlignmentState.trajectoryClass i => stepTransform h step i
```

The mediator tracks the same step-relative coordinate as the R2 target.  The
uniform dimension is the codomain size `n`.

## Canonical Dynamic Pair

For `h : 1 < n`, define:

```lean
def x_alignment {n : Nat} (h : 1 < n) : AlignmentState n :=
  AlignmentState.trajectoryClass (firstTrajectory h)

def y_alignment {n : Nat} (h : 1 < n) : AlignmentState n :=
  AlignmentState.trajectoryClass (secondTrajectory h)
```

Then prove for every step:

```lean
requiredAtStep_alignment :
  RequiredDistinction ((target_alignment h).targetAt step)
    (x_alignment h) (y_alignment h)

jointSameAtStep_alignment :
  JointSame obs_alignment I_alignment
    (x_alignment h) (y_alignment h)

dynamicDiagonalWitness_alignment :
  DynamicDiagonalizationWitness obs_alignment (target_alignment h) I_alignment
    step (x_alignment h) (y_alignment h)
```

## Dynamic Residual Nonempty

Prove:

```lean
dynamicResidualNonempty_alignment :
  ∀ step : AlignmentStep,
    DynamicResidualNonempty_R2 obs_alignment (target_alignment h) I_alignment step
```

Interpretation:

```text
at each dynamic step, visible observation leaves a nonempty R2 residual.
```

## Dynamic Mediated Closure

Prove:

```lean
dynamicMediatedResidualEmpty_M_alignment :
  ∀ step : AlignmentStep,
    DynamicMediatedResidualEmpty obs_alignment (target_alignment h) I_alignment
      step ((M_alignment h) step)
```

Proof idea:

```text
if targetAt step x != targetAt step y, then M step x != M step y.
```

In the complete dynamic version this follows from injectivity of
`stepTransform h step`.

## Uniform Proper Dynamic Certificate

The core dynamic certificate is:

```lean
uniformProperMediatedR2Certificate_M_alignment :
  UniformProperMediatedR2Certificate
    obs_alignment (target_alignment h) I_alignment (M_alignment h)
```

It must prove:

```text
for every step:
  residual exists;
  mediator closes;
  mediator is irreducible.
```

This is the first theorem that strictly requires the dynamic file.

## Marginal Non-Descent

The proof must expose non-descent to visible marginal readers at every step.

```lean
no_descent_terminal_only_alignment :
  ∀ step : AlignmentStep,
    ¬ MediatorDescendsSubfamily
      obs_alignment I_alignment_terminal_only ((M_alignment h) step)

no_descent_prompt_only_alignment :
  ∀ step : AlignmentStep,
    ¬ MediatorDescendsSubfamily
      obs_alignment I_alignment_prompt_only ((M_alignment h) step)
```

Also expose witnessed versions:

```lean
witness_no_descent_terminal_only_alignment :
  ∀ step : AlignmentStep,
    MediatorNonDescentWitness
      obs_alignment I_alignment_terminal_only ((M_alignment h) step)

witness_no_descent_prompt_only_alignment :
  ∀ step : AlignmentStep,
    MediatorNonDescentWitness
      obs_alignment I_alignment_prompt_only ((M_alignment h) step)
```

This prevents the phrase “marginal interfaces fail” from being only informal.

## Exact Uniform Dimension `n`

At each step, any mediated closure:

```lean
M : AlignmentState n -> Fin m
```

must induce an injection:

```lean
Fin n -> Fin m
```

by:

```lean
fun i => M (AlignmentState.trajectoryClass i)
```

The proof uses:

```text
trajectoryClass i and trajectoryClass j are R1-indistinguishable;
if M identifies them, mediated closure contradicts targetAt step i != targetAt
step j.
```

Then use:

```lean
FiniteDimensionHierarchy.no_injective_fin_of_lt
```

to prove:

```lean
no_smaller_properMediatedR2Certificate_alignment_at_step :
  ∀ step : AlignmentStep,
    ∀ m : Nat,
      m < n ->
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_alignment ((target_alignment h).targetAt step) I_alignment m
```

Then expose:

```lean
exactProperMediatedR2Dimension_n_alignment_at_step :
  ∀ step : AlignmentStep,
    ExactProperMediatedR2Dimension
      obs_alignment ((target_alignment h).targetAt step) I_alignment n
```

This is exact dimension at every dynamic step.  The dimension is uniform
because the same `n` works for all steps.

## Dynamic Compatibility Profile

To connect with alignment language, define a compatibility predicate.  The
predicate must receive the nontriviality proof `h : 1 < n`, because it uses
the canonical first trajectory.  This is a binary `Prop`-valued compatibility
predicate, so its exact compatibility dimension is `2`, not `n`.

```lean
def compatible_alignment {n : Nat} (h : 1 < n) :
    AlignmentStep -> AlignmentState n -> Prop :=
  fun step s =>
    (target_alignment h).targetAt step s =
      stepTransform h step (firstTrajectory h)
```

This says that a state is compatible at `step` when its step-relative target
coordinate is the transformed canonical first trajectory.

Then prove:

```lean
stepSeparatesFiber_alignment :
  ∀ step : AlignmentStep,
    StepSeparatesFiber obs_alignment I_alignment
      (compatible_alignment h) step
```

and:

```lean
familyIrreducibleCompatibilityProfile_alignment :
  ∀ step : AlignmentStep,
    FamilyIrreducibleCompatibilityProfile
      obs_alignment I_alignment (compatible_alignment h) step 2
```

This layer proves that dynamic compatibility itself cannot be predicted from
visible subfamilies, and that an exact binary finite refining lift is required.

The proof of exact compatibility dimension `2` should be explicit:

```lean
compatDimLe_two_alignment :
  ∀ step : AlignmentStep,
    CompatDimLe (compatible_alignment h) step 2

not_compatDimLe_zero_alignment :
  ∀ step : AlignmentStep,
    ¬ CompatDimLe (compatible_alignment h) step 0

not_compatDimLe_one_alignment :
  ∀ step : AlignmentStep,
    ¬ CompatDimLe (compatible_alignment h) step 1

compatDimEq_two_alignment :
  ∀ step : AlignmentStep,
    CompatDimEq (compatible_alignment h) step 2
```

The lower bounds for `0` and `1` should use the existing dynamic lemmas from
`StepSeparatesFiber`; the upper bound uses the obvious two-valued classifier.

Important separation of invariants:

```text
Exact trajectory mediator dimension: n
Exact compatibility classifier dimension: 2
```

The `n`-dimensional result belongs to R2 trajectory mediation.  The
compatibility profile is a separate Boolean access theorem.

Use the existing theorem:

```lean
endToEnd_familyIrreducibleCompatibilityProfile_subset
```

with a visible base map:

```lean
def base_alignment {n : Nat} : AlignmentState n -> Unit :=
  fun _ => ()
```

to expose:

```text
separated active fiber;
exact refining lift dimension 2;
no smaller lift;
no descent to any subfamily included in I.
```

## Dynamic Residual Profile Layer

The complete dynamic target must add a residual profile after the uniform
certificate compiles.

Use:

```lean
DynamicResidualProfile
DynamicResidualCoordinate
StableResidualSection
DynamicResidualClosureBridge
```

Goal:

```text
turn stepwise residual witnesses into a transportable dynamic residual
profile.
```

Use concrete profile types in the first implementation:

```lean
abbrev AlignmentResidualState (n : Nat) :=
  AlignmentState n × AlignmentState n

abbrev AlignmentHorizon := AlignmentStep
abbrev AlignmentDynamicTime := AlignmentStep

inductive AlignmentWindow
  | all
```

The residual predicate should be the pairwise dynamic residual:

```lean
ResidualAt r W p :=
  DynamicResidual_R2 obs_alignment (target_alignment h) I_alignment
    r p.1 p.2
```

`InWindow` is trivial for `AlignmentWindow.all`.  The first transport profile
uses identity state transport on residual pairs:

```lean
stepState p = p
```

This is legitimate because injectivity of `stepTransform h step` makes every
pair of distinct trajectory classes remain R2-distinct at every step.  The
profile must prove the required `restrict`, `persist`, and `transport` fields
from that fact, not assume them informally.

This layer must not pretend global closure is automatic.  It must use an
explicit bridge:

```lean
DynamicResidualClosureBridge
```

The bridge stores:

```text
GlobalNonClosure -> StableResidualSection
(GlobalNonClosure -> False) -> GlobalClosure
```

So the global theorem is conditional on a real extraction principle.

Required profile theorem:

```lean
dynamicResidualProfile_alignment :
  DynamicResidualProfile
    (AlignmentResidualState n) AlignmentHorizon
    AlignmentDynamicTime AlignmentWindow
```

Required coordinate theorem:

```lean
dynamicResidualCoordinate_alignment :
  DynamicResidualCoordinate dynamicResidualProfile_alignment
```

Required bridge theorem, if global closure is claimed:

```lean
globalClosure_alignment_of_noStableResidualSection :
  NoStableResidualSection dynamicResidualProfile_alignment ->
    bridge_alignment.GlobalClosure
```

Without this bridge, the file may claim stepwise and uniform dynamic closure,
but not global closure.

## End-To-End Dynamic Theorem

Expose a final dynamic theorem:

```lean
theorem endToEnd_dynamic_alignment
    {n : Nat} (h : 1 < n) :
    UniformProperMediatedR2Certificate
      obs_alignment (target_alignment h) I_alignment (M_alignment h)
      ∧ (∀ step : AlignmentStep,
          ExactProperMediatedR2Dimension
            obs_alignment ((target_alignment h).targetAt step) I_alignment n)
      ∧ (∀ step : AlignmentStep,
          ¬ MediatorDescendsSubfamily
            obs_alignment I_alignment_terminal_only ((M_alignment h) step))
      ∧ (∀ step : AlignmentStep,
          ¬ MediatorDescendsSubfamily
            obs_alignment I_alignment_prompt_only ((M_alignment h) step))
```

Interpretation:

```text
visible dynamic alignment observations leave a stepwise trajectory residual;
a step-indexed causal mediator closes it;
the exact proper mediated dimension is uniformly n;
visible marginal interfaces do not recover the mediator.
```

## Axiom Audit

The file must end with:

```lean
/- AXIOM_AUDIT_BEGIN -/
#print axioms ...
/- AXIOM_AUDIT_END -/
```

Audit at least:

```lean
AlignmentStep
AlignmentState
AlignmentInterface
AlignmentObservation
obs_alignment
target_alignment
M_alignment
dynamicDiagonalWitness_alignment
dynamicResidualNonempty_alignment
dynamicMediatedResidualEmpty_M_alignment
uniformProperMediatedR2Certificate_M_alignment
no_descent_terminal_only_alignment
no_descent_prompt_only_alignment
exactProperMediatedR2Dimension_n_alignment_at_step
endToEnd_dynamic_alignment
```

Expected output:

```text
does not depend on any axioms
```

## Bridge To Real LLMs

Only after the dynamic Lean theorem exists should the empirical bridge be
specified.

The bridge must define a certificate format mapping ASLMT or transformer logs
to the Lean objects:

```text
run id / context id       -> AlignmentStep
latent causal selection   -> Fin n trajectory coordinate
terminal output / answer  -> TerminalOutput
prompt/task class         -> PromptClass
local/global arbitration  -> M step
OOD success trace         -> evidence for residual closure
```

Required bridge artifacts:

```text
1. a JSONL or certificate schema;
2. a parser/checker;
3. a statement of which Lean predicates are being witnessed;
4. a proof or trusted-check boundary for the extraction process.
```

The Lean theorem proves the structure.  The empirical bridge must prove or
certify that a concrete run instantiates the structure.

## What This Would Prove

The dynamic Lean file would prove:

```text
There are dynamic alignment states with identical visible observations but
distinct causal trajectories at every step.
```

It would also prove:

```text
For every n >= 2, the exact uniform mediated dimension needed to close the
dynamic trajectory residual can be n.
```

With the compatibility profile, it would prove:

```text
visible subfamilies cannot predict the dynamic compatibility coordinate
without an exact finite refining lift.
```

## What It Would Still Not Prove

Even after this dynamic Lean file compiles, it would still not prove:

```text
real LLMs have exactly this carrier;
real transformer internals instantiate this model;
empirical ASLMT logs satisfy the Lean definitions;
alignment is solved for deployed systems.
```

Those claims require the empirical bridge and, for deployed alignment, a
system-level specification beyond this repository.

## Acceptance Criteria

The dynamic target is complete only when:

1. `LLMAlignmentDynamicR1R2.lean` compiles.
2. `lake build` passes.
3. `R1R2proof.lean` imports `LLMAlignmentDynamicR1R2`.
4. The file imports `DynamicRegimesSelfContained`.
5. The theorem `uniformProperMediatedR2Certificate_M_alignment` exists.
6. The theorem `exactProperMediatedR2Dimension_n_alignment_at_step` exists.
7. Explicit terminal-only and prompt-only non-descent theorems exist for every
   step.
8. The compatibility-profile theorem exists.
9. A `DynamicResidualProfile` and `DynamicResidualCoordinate` exist, so the
   residual is represented as transportable dynamic data.
10. Any global-closure claim factors through `DynamicResidualClosureBridge`.
11. The axiom audit prints no dependency on arbitrary axioms.
12. The README states the dynamic theorem without claiming empirical LLM
    alignment is solved by the Lean file alone.
