import DynamicRegimesSelfContained
import FiniteDimensionHierarchy

/-!
# Dynamic LLM/R1R2 alignment instance

This file instantiates the dynamic R1/R2 framework on an abstract alignment
carrier.

The carrier is intentionally finite and auditable:

* states are causal trajectory classes;
* visible R1 interfaces read only prompt/terminal observations;
* a dynamic step carries an injective finite transform of trajectory classes;
* the R2 target reads the step-relative trajectory coordinate;
* the mediator reads the same step-relative coordinate.

For every `n` with `1 < n`, every dynamic step has exact proper mediated R2
dimension `n`.  The same `n` is uniform across steps.

The file also records the Boolean compatibility layer separately: a
`Prop`-valued compatibility predicate has exact classifier dimension `2`, not
`n`.  Thus the two invariants are kept distinct:

```text
trajectory mediation dimension      = n
compatibility classifier dimension  = 2
```

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace LLMAlignmentDynamicR1R2

open Standalone.DynamicRegimesSelfContained

/-- A dynamic step carries an injective transform of trajectory coordinates. -/
structure AlignmentStep (n : Nat) where
  transform : Fin n → Fin n
  transform_injective : Function.Injective transform

/-- Causal trajectory states. -/
inductive AlignmentState (n : Nat)
  | trajectoryClass : Fin n → AlignmentState n

/-- Visible terminal output class. -/
inductive TerminalOutput
  | sameVisibleOutput
deriving DecidableEq

/-- Visible prompt/task class. -/
inductive PromptClass
  | samePromptClass
deriving DecidableEq

/-- Visible R1 interfaces. -/
inductive AlignmentInterface
  | terminalOutputReader
  | promptClassReader
deriving DecidableEq

/-- Observations returned by visible interfaces. -/
inductive AlignmentObservation
  | terminalOutput : TerminalOutput → AlignmentObservation
  | promptClass : PromptClass → AlignmentObservation
deriving DecidableEq

/-- The full visible active interface family. -/
def I_alignment : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => True
  | AlignmentInterface.promptClassReader => True

/-- The terminal-output marginal subfamily. -/
def I_alignment_terminal_only : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => True
  | AlignmentInterface.promptClassReader => False

/-- The prompt-class marginal subfamily. -/
def I_alignment_prompt_only : Subfamily AlignmentInterface
  | AlignmentInterface.terminalOutputReader => False
  | AlignmentInterface.promptClassReader => True

/-- Terminal-only is a proper active subfamily. -/
theorem terminal_only_proper_alignment :
    Subfamily.Proper I_alignment_terminal_only I_alignment := by
  constructor
  · intro j hj
    cases j
    · trivial
    · cases hj
  · exact
      ⟨AlignmentInterface.promptClassReader,
        trivial,
        by
          intro h
          cases h⟩

/-- Prompt-only is a proper active subfamily. -/
theorem prompt_only_proper_alignment :
    Subfamily.Proper I_alignment_prompt_only I_alignment := by
  constructor
  · intro j hj
    cases j
    · cases hj
    · trivial
  · exact
      ⟨AlignmentInterface.terminalOutputReader,
        trivial,
        by
          intro h
          cases h⟩

/--
The visible R1 observation deliberately forgets the trajectory coordinate.
-/
def obs_alignment {n : Nat} :
    AlignmentInterface → AlignmentState n → AlignmentObservation
  | AlignmentInterface.terminalOutputReader, _ =>
      AlignmentObservation.terminalOutput TerminalOutput.sameVisibleOutput
  | AlignmentInterface.promptClassReader, _ =>
      AlignmentObservation.promptClass PromptClass.samePromptClass

/-- All trajectory states are indistinguishable by the full visible R1 family. -/
theorem jointSame_alignmentStates
    {n : Nat} (i j : Fin n) :
    JointSame (obs_alignment (n := n)) I_alignment
      (AlignmentState.trajectoryClass i)
      (AlignmentState.trajectoryClass j) := by
  intro interface _hInterface
  cases interface <;> rfl

/-- All trajectory states are indistinguishable by every visible subfamily. -/
theorem jointSame_alignmentStates_subfamily
    {n : Nat} (K : Subfamily AlignmentInterface) (i j : Fin n) :
    JointSame (obs_alignment (n := n)) K
      (AlignmentState.trajectoryClass i)
      (AlignmentState.trajectoryClass j) := by
  intro interface _hInterface
  cases interface <;> rfl

/-- First canonical trajectory, available in every dimension at least two. -/
def firstTrajectory {n : Nat} (h : 1 < n) : Fin n :=
  ⟨0, Nat.lt_trans Nat.zero_lt_one h⟩

/-- Second canonical trajectory, available in every dimension at least two. -/
def secondTrajectory {n : Nat} (h : 1 < n) : Fin n :=
  ⟨1, h⟩

/-- The two canonical trajectories are distinct. -/
theorem firstTrajectory_ne_secondTrajectory
    {n : Nat} (h : 1 < n) :
    firstTrajectory h ≠ secondTrajectory h := by
  intro hEq
  have hVal : (0 : Nat) = 1 := congrArg Fin.val hEq
  cases hVal

/-- First canonical alignment state. -/
def x_alignment {n : Nat} (h : 1 < n) : AlignmentState n :=
  AlignmentState.trajectoryClass (firstTrajectory h)

/-- Second canonical alignment state. -/
def y_alignment {n : Nat} (h : 1 < n) : AlignmentState n :=
  AlignmentState.trajectoryClass (secondTrajectory h)

/-- Dynamic R2 target: read the step-relative trajectory coordinate. -/
def target_alignment {n : Nat} :
    DynamicTarget (AlignmentState n) (AlignmentStep n) (Fin n) :=
  { targetAt := fun step state =>
      match state with
      | AlignmentState.trajectoryClass i => step.transform i }

/-- Step-indexed mediator: the same step-relative trajectory coordinate. -/
def M_alignment {n : Nat} :
    AlignmentStep n → AlignmentState n → Fin n :=
  fun step state =>
    match state with
    | AlignmentState.trajectoryClass i => step.transform i

/-- The dynamic step separates the two canonical trajectories. -/
theorem requiredAtStep_alignment
    {n : Nat} (h : 1 < n) (step : AlignmentStep n) :
    RequiredDistinction (target_alignment.targetAt step)
      (x_alignment h) (y_alignment h) := by
  intro hTarget
  exact firstTrajectory_ne_secondTrajectory h
    (step.transform_injective hTarget)

/-- The canonical pair is visibly identical at every step. -/
theorem jointSameAtStep_alignment
    {n : Nat} (h : 1 < n) (_step : AlignmentStep n) :
    JointSame (obs_alignment (n := n)) I_alignment
      (x_alignment h) (y_alignment h) := by
  exact jointSame_alignmentStates _ _

/-- The canonical pair is a dynamic diagonalization witness at every step. -/
theorem dynamicDiagonalWitness_alignment
    {n : Nat} (h : 1 < n) (step : AlignmentStep n) :
    DynamicDiagonalizationWitness
      (obs_alignment (n := n)) (target_alignment (n := n))
      I_alignment step (x_alignment h) (y_alignment h) := by
  exact ⟨requiredAtStep_alignment h step, jointSameAtStep_alignment h step⟩

/-- Every dynamic step has a nonempty R2 residual before mediation. -/
theorem dynamicResidualNonempty_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      DynamicResidualNonempty_R2
        (obs_alignment (n := n)) (target_alignment (n := n))
        I_alignment step := by
  intro step
  exact ⟨x_alignment h, y_alignment h, dynamicDiagonalWitness_alignment h step⟩

/-- The step-indexed mediator closes every dynamic residual. -/
theorem dynamicMediatedResidualEmpty_M_alignment
    {n : Nat} :
    ∀ step : AlignmentStep n,
      DynamicMediatedResidualEmpty
        (obs_alignment (n := n)) (target_alignment (n := n))
        I_alignment step (M_alignment step) := by
  intro step x y hResidual
  exact hResidual.1 hResidual.2.2

/-- The mediator separates the canonical pair at every step. -/
theorem M_alignment_separates_canonical
    {n : Nat} (h : 1 < n) (step : AlignmentStep n) :
    M_alignment step (x_alignment h) ≠ M_alignment step (y_alignment h) := by
  exact requiredAtStep_alignment h step

/-- Terminal-only non-descent witness at every step. -/
theorem witness_no_descent_terminal_only_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      MediatorNonDescentWitness
        (obs_alignment (n := n)) I_alignment_terminal_only
        (M_alignment step) := by
  intro step
  exact
    ⟨x_alignment h, y_alignment h,
      jointSame_alignmentStates_subfamily I_alignment_terminal_only _ _,
      M_alignment_separates_canonical h step⟩

/-- Prompt-only non-descent witness at every step. -/
theorem witness_no_descent_prompt_only_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      MediatorNonDescentWitness
        (obs_alignment (n := n)) I_alignment_prompt_only
        (M_alignment step) := by
  intro step
  exact
    ⟨x_alignment h, y_alignment h,
      jointSame_alignmentStates_subfamily I_alignment_prompt_only _ _,
      M_alignment_separates_canonical h step⟩

/-- Terminal-only does not recover the mediator at any step. -/
theorem no_descent_terminal_only_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      ¬ MediatorDescendsSubfamily
        (obs_alignment (n := n)) I_alignment_terminal_only
        (M_alignment step) := by
  intro step hDescends
  rcases witness_no_descent_terminal_only_alignment h step with
    ⟨x, y, hSame, hNe⟩
  exact hNe (hDescends x y hSame)

/-- Prompt-only does not recover the mediator at any step. -/
theorem no_descent_prompt_only_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      ¬ MediatorDescendsSubfamily
        (obs_alignment (n := n)) I_alignment_prompt_only
        (M_alignment step) := by
  intro step hDescends
  rcases witness_no_descent_prompt_only_alignment h step with
    ⟨x, y, hSame, hNe⟩
  exact hNe (hDescends x y hSame)

/-- Witness-style irreducibility of the step-indexed mediator. -/
theorem witnessedIrreducibleMediator_M_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      WitnessedIrreducibleMediator
        (obs_alignment (n := n)) I_alignment (M_alignment step) := by
  intro step K _hProper
  exact
    ⟨x_alignment h, y_alignment h,
      jointSame_alignmentStates_subfamily K _ _,
      M_alignment_separates_canonical h step⟩

/-- Irreducibility of the step-indexed mediator. -/
theorem irreducibleMediator_M_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      IrreducibleMediator
        (obs_alignment (n := n)) I_alignment (M_alignment step) := by
  intro step
  exact witnessedIrreducibleMediator_irreducibleMediator
    (obs_alignment (n := n)) I_alignment (M_alignment step)
    (witnessedIrreducibleMediator_M_alignment h step)

/-- Stepwise proper mediated R2 certificate. -/
theorem stepwiseProperMediatedR2Certificate_M_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      StepwiseProperMediatedR2Certificate
        (obs_alignment (n := n)) (target_alignment (n := n))
        I_alignment step (M_alignment step) := by
  intro step
  exact
    ⟨dynamicResidualNonempty_alignment h step,
      dynamicMediatedResidualEmpty_M_alignment step,
      irreducibleMediator_M_alignment h step⟩

/-- Uniform proper mediated dynamic certificate. -/
theorem uniformProperMediatedR2Certificate_M_alignment
    {n : Nat} (h : 1 < n) :
    UniformProperMediatedR2Certificate
      (obs_alignment (n := n)) (target_alignment (n := n))
      I_alignment (M_alignment (n := n)) := by
  exact
    ⟨dynamicResidualNonempty_alignment h,
      dynamicMediatedResidualEmpty_M_alignment,
      irreducibleMediator_M_alignment h⟩

/--
Any mediated closure at a step induces an injection from trajectory
coordinates into the mediator codomain.
-/
theorem injective_of_mediatedResidualEmpty_alignment
    {n m : Nat} (step : AlignmentStep n) {M : AlignmentState n → Fin m} :
    MediatedResidualEmpty
      (obs_alignment (n := n)) (target_alignment.targetAt step)
      I_alignment M →
      Function.Injective (fun i : Fin n => M (AlignmentState.trajectoryClass i)) := by
  intro hCloses i j hM
  by_cases hEq : i = j
  · exact hEq
  · have hReq :
        RequiredDistinction (target_alignment.targetAt step)
          (AlignmentState.trajectoryClass i)
          (AlignmentState.trajectoryClass j) := by
      intro hTarget
      exact hEq (step.transform_injective hTarget)
    have hResidual :
        MediatedResidual
          (obs_alignment (n := n)) (target_alignment.targetAt step)
          I_alignment M
          (AlignmentState.trajectoryClass i)
          (AlignmentState.trajectoryClass j) :=
      ⟨hReq, ⟨jointSame_alignmentStates i j, hM⟩⟩
    exact False.elim (hCloses _ _ hResidual)

/-- No smaller proper mediated certificate can close a dynamic step. -/
theorem no_smaller_properMediatedR2Certificate_alignment_at_step
    {n : Nat} :
    ∀ step : AlignmentStep n,
      ∀ m : Nat,
        m < n →
          ¬ ExistsProperMediatedR2CertificateAtDim
            (obs_alignment (n := n)) (target_alignment.targetAt step)
            I_alignment m := by
  intro step m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (AlignmentState.trajectoryClass i)) :=
    injective_of_mediatedResidualEmpty_alignment step hCert.closes
  exact (FiniteDimensionHierarchy.no_injective_fin_of_lt n m hm
    (fun i : Fin n => M (AlignmentState.trajectoryClass i))) hInjective

/-- Dimension-minimal proper certificate at each dynamic step. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_alignment_at_step
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      DimensionMinimalProperMediatedR2Certificate
        (obs_alignment (n := n)) (target_alignment.targetAt step)
        I_alignment (M_alignment step) := by
  intro step
  exact
    ⟨stepwiseProperMediatedR2Certificate_M_alignment h step,
      no_smaller_properMediatedR2Certificate_alignment_at_step step⟩

/-- Exact proper mediated R2 dimension at each dynamic step. -/
theorem exactProperMediatedR2Dimension_n_alignment_at_step
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      ExactProperMediatedR2Dimension
        (obs_alignment (n := n)) (target_alignment.targetAt step)
        I_alignment n := by
  intro step
  exact exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M_alignment_at_step h step)

/-- Dynamic exact proper mediated R2 dimension at each step. -/
theorem dynamicExactProperMediatedR2Dimension_n_alignment_at_step
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      DynamicExactProperMediatedR2Dimension
        (obs_alignment (n := n)) (target_alignment (n := n))
        I_alignment step n := by
  intro step
  exact exactProperMediatedR2Dimension_n_alignment_at_step h step

/-- Compatibility with the transformed first trajectory. -/
def compatible_alignment {n : Nat} (h : 1 < n) :
    AlignmentStep n → AlignmentState n → Prop :=
  fun step state =>
    target_alignment.targetAt step state =
      step.transform (firstTrajectory h)

/-- The dynamic step separates the compatibility fiber. -/
theorem stepSeparatesFiber_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      StepSeparatesFiber
        (obs_alignment (n := n)) I_alignment
        (compatible_alignment h) step := by
  intro step
  refine ⟨x_alignment h, y_alignment h, ?_, ?_, ?_⟩
  · exact jointSameAtStep_alignment h step
  · rfl
  · intro hCompat
    exact firstTrajectory_ne_secondTrajectory h
      (step.transform_injective hCompat.symm)

/-- The first point of `Fin 2`. -/
def fin2Zero : Fin 2 :=
  ⟨0, by decide⟩

/-- The second point of `Fin 2`. -/
def fin2One : Fin 2 :=
  ⟨1, by decide⟩

/-- Finite classifier for the Boolean compatibility predicate. -/
def compatibilityReadout {n : Nat} (h : 1 < n)
    (step : AlignmentStep n) (state : AlignmentState n) : Fin 2 :=
  match state with
  | AlignmentState.trajectoryClass i =>
      if step.transform i = step.transform (firstTrajectory h) then
        fin2Zero
      else
        fin2One

/-- Predicate selecting the compatible point in `Fin 2`. -/
def compatibilityPred (a : Fin 2) : Prop :=
  a = fin2Zero

/-- The compatibility classifier has dimension at most two. -/
theorem compatDimLe_two_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      CompatDimLe (compatible_alignment h) step 2 := by
  intro step
  refine ⟨compatibilityReadout h step, compatibilityPred, ?_⟩
  intro state
  cases state with
  | trajectoryClass i =>
      by_cases hCompat : step.transform i = step.transform (firstTrajectory h)
      · constructor
        · intro _hLeft
          unfold compatibilityReadout compatibilityPred
          change (if step.transform i = step.transform (firstTrajectory h) then
              fin2Zero else fin2One) = fin2Zero
          rw [if_pos hCompat]
        · intro _hRight
          exact hCompat
      · constructor
        · intro hLeft
          exact False.elim (hCompat hLeft)
        · intro hRight
          unfold compatibilityReadout compatibilityPred at hRight
          change (if step.transform i = step.transform (firstTrajectory h) then
              fin2Zero else fin2One) = fin2Zero at hRight
          rw [if_neg hCompat] at hRight
          have hVal : (1 : Nat) = 0 := congrArg Fin.val hRight
          cases hVal

/-- The compatibility classifier cannot have dimension zero. -/
theorem not_compatDimLe_zero_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      ¬ CompatDimLe (compatible_alignment h) step 0 := by
  intro step
  exact not_compatDimLe_zero_of_stepSeparatesFiber
    (obs_alignment (n := n)) I_alignment
    (compatible_alignment h) step
    (stepSeparatesFiber_alignment h step)

/-- The compatibility classifier cannot have dimension one. -/
theorem not_compatDimLe_one_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      ¬ CompatDimLe (compatible_alignment h) step 1 := by
  intro step
  exact not_compatDimLe_one_of_stepSeparatesFiber
    (obs_alignment (n := n)) I_alignment
    (compatible_alignment h) step
    (stepSeparatesFiber_alignment h step)

/-- The Boolean compatibility classifier has exact dimension two. -/
theorem compatDimEq_two_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      CompatDimEq (compatible_alignment h) step 2 := by
  intro step
  constructor
  · exact compatDimLe_two_alignment h step
  · intro m hm
    cases m with
    | zero =>
        exact not_compatDimLe_zero_alignment h step
    | succ m =>
        cases m with
        | zero =>
            exact not_compatDimLe_one_alignment h step
        | succ m =>
            have hLtOne : Nat.succ m < 1 :=
              Nat.lt_of_succ_lt_succ hm
            have hLtZero : m < 0 :=
              Nat.lt_of_succ_lt_succ hLtOne
            exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Compatibility-oriented dynamic family profile at each step. -/
theorem familyIrreducibleCompatibilityProfile_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      FamilyIrreducibleCompatibilityProfile
        (obs_alignment (n := n)) I_alignment
        (compatible_alignment h) step 2 := by
  intro step
  exact ⟨stepSeparatesFiber_alignment h step, compatDimEq_two_alignment h step⟩

/-- Visible base retained by a refining lift. -/
def base_alignment {n : Nat} (_state : AlignmentState n) : Unit :=
  ()

/-- End-to-end compatibility access theorem at each step. -/
theorem endToEnd_compatibility_alignment
    {n : Nat} (h : 1 < n) :
    ∀ step : AlignmentStep n,
      StepSeparatesFiber
          (obs_alignment (n := n)) I_alignment
          (compatible_alignment h) step
        ∧ RefiningLift base_alignment (compatible_alignment h) step 2
        ∧ (∀ m : Nat, m < 2 →
            ¬ RefiningLift base_alignment (compatible_alignment h) step m)
        ∧ (∀ L : RefiningLiftData
              (S := AlignmentState n) (Base := Unit) (Step := AlignmentStep n)
              (base := base_alignment) (compatible := compatible_alignment h)
              step 2,
            ∀ K : Subfamily AlignmentInterface, Subfamily.Subset K I_alignment →
              ¬ DynamicMediatorDescendsSubfamily
                (obs_alignment (n := n)) K
                (fun x : AlignmentState n => (L.extObs x).2)) := by
  intro step
  exact endToEnd_familyIrreducibleCompatibilityProfile_subset
    (obs_alignment (n := n)) base_alignment I_alignment
    (compatible_alignment h) step 2
    (familyIrreducibleCompatibilityProfile_alignment h step)

/-- Residual states are pairs of alignment states. -/
abbrev AlignmentResidualState (n : Nat) :=
  AlignmentState n × AlignmentState n

/-- Dynamic residual horizons are alignment steps. -/
abbrev AlignmentHorizon (n : Nat) :=
  AlignmentStep n

/-- Dynamic residual time points are alignment steps. -/
abbrev AlignmentDynamicTime (n : Nat) :=
  AlignmentStep n

/-- The first profile uses one global window. -/
inductive AlignmentWindow
  | all

/-- Pairwise dynamic residual predicate. -/
def alignmentResidualAt {n : Nat} (_h : 1 < n)
    (r : AlignmentHorizon n) (_W : AlignmentWindow)
    (p : AlignmentResidualState n) : Prop :=
  DynamicResidual_R2
    (obs_alignment (n := n)) (target_alignment (n := n))
    I_alignment r p.1 p.2

/-- Transportable dynamic residual profile. -/
def dynamicResidualProfile_alignment
    {n : Nat} (h : 1 < n) :
    DynamicResidualProfile
      (AlignmentResidualState n) (AlignmentHorizon n)
      (AlignmentDynamicTime n) AlignmentWindow :=
  { stepState := fun p => p
    nextHorizon := fun r => r
    nextTime := fun k => k
    InWindow := fun _W _p => True
    WindowLe := fun _W _W' => True
    ResidualAt := alignmentResidualAt h
    restrict := by
      intro r W W' x _hLe _hIn hResidual
      exact hResidual
    persist := by
      intro r W x hResidual
      exact hResidual
    transport := by
      intro r W x hResidual
      exact ⟨AlignmentWindow.all, trivial, hResidual⟩ }

/-- Positive coordinate for the dynamic residual profile. -/
def dynamicResidualCoordinate_alignment
    {n : Nat} (h : 1 < n) :
    DynamicResidualCoordinate (dynamicResidualProfile_alignment h) :=
  { rhoAt := fun _r _W => 1
    positive_of_residual := by
      intro r W x _hIn _hResidual
      exact Nat.succ_pos 0
    witness_of_positive := by
      intro r W _hPositive
      exact
        ⟨(x_alignment h, y_alignment h),
          trivial,
          dynamicDiagonalWitness_alignment h r⟩ }

/-- Existence of a transportable dynamic residual profile with coordinate. -/
def HasTransportableResidualProfile
    {n : Nat} (_h : 1 < n) : Prop :=
  Nonempty (Sigma fun profile :
      DynamicResidualProfile
        (AlignmentResidualState n) (AlignmentHorizon n)
        (AlignmentDynamicTime n) AlignmentWindow =>
    DynamicResidualCoordinate profile)

/--
Formal alignedness for this dynamic R1/R2 carrier.

Aligned means: uniform proper mediated closure, exact mediated dimension at
each step, blocked descent to the two visible marginal readers, and a
transportable residual profile.
-/
def Aligned {n : Nat} (h : 1 < n) : Prop :=
  UniformProperMediatedR2Certificate
    (obs_alignment (n := n)) (target_alignment (n := n))
    I_alignment (M_alignment (n := n))
    ∧ (∀ step : AlignmentStep n,
        ExactProperMediatedR2Dimension
          (obs_alignment (n := n)) (target_alignment.targetAt step)
          I_alignment n)
    ∧ (∀ step : AlignmentStep n,
        ¬ MediatorDescendsSubfamily
          (obs_alignment (n := n)) I_alignment_terminal_only
          (M_alignment step))
    ∧ (∀ step : AlignmentStep n,
        ¬ MediatorDescendsSubfamily
          (obs_alignment (n := n)) I_alignment_prompt_only
          (M_alignment step))
    ∧ HasTransportableResidualProfile h

/-- Certificate object for the formal alignedness predicate. -/
structure DynamicAlignmentCertificate
    {n : Nat} (h : 1 < n) : Prop where
  uniform_certificate :
    UniformProperMediatedR2Certificate
      (obs_alignment (n := n)) (target_alignment (n := n))
      I_alignment (M_alignment (n := n))
  exact_dimension :
    ∀ step : AlignmentStep n,
      ExactProperMediatedR2Dimension
        (obs_alignment (n := n)) (target_alignment.targetAt step)
        I_alignment n
  terminal_marginal_blocked :
    ∀ step : AlignmentStep n,
      ¬ MediatorDescendsSubfamily
        (obs_alignment (n := n)) I_alignment_terminal_only
        (M_alignment step)
  prompt_marginal_blocked :
    ∀ step : AlignmentStep n,
      ¬ MediatorDescendsSubfamily
        (obs_alignment (n := n)) I_alignment_prompt_only
        (M_alignment step)
  transportable_residual_profile :
    HasTransportableResidualProfile h

/-- The concrete residual profile and coordinate are present. -/
theorem hasTransportableResidualProfile_alignment
    {n : Nat} (h : 1 < n) :
    HasTransportableResidualProfile h := by
  exact ⟨⟨dynamicResidualProfile_alignment h,
    dynamicResidualCoordinate_alignment h⟩⟩

/-- A dynamic R1/R2 alignment certificate proves formal alignedness. -/
theorem aligned_of_dynamicR1R2Certificate
    {n : Nat} {h : 1 < n} :
    DynamicAlignmentCertificate h → Aligned h := by
  intro cert
  exact
    ⟨cert.uniform_certificate,
      cert.exact_dimension,
      cert.terminal_marginal_blocked,
      cert.prompt_marginal_blocked,
      cert.transportable_residual_profile⟩

/-- The concrete dynamic system has a complete alignment certificate. -/
theorem dynamicAlignmentCertificate_alignment
    {n : Nat} (h : 1 < n) :
    DynamicAlignmentCertificate h := by
  exact
    ⟨uniformProperMediatedR2Certificate_M_alignment h,
      exactProperMediatedR2Dimension_n_alignment_at_step h,
      no_descent_terminal_only_alignment h,
      no_descent_prompt_only_alignment h,
      hasTransportableResidualProfile_alignment h⟩

/-
External bridge layer.

This is the formal boundary between the abstract dynamic carrier above and an
external system such as an empirical ASLMT run.  The external system is not
accepted by name: it must provide a finite causal trajectory coordinate, a
representative state for every coordinate, and injective step transforms.
-/

/--
Bridge data from an external carrier into the R1/R2 trajectory interface.

The `representative` field is essential for the exact lower bound: without a
state realizing each point of `Fin n`, the file could prove closure but not
that dimension `n` is necessary.
-/
structure ExternalAlignmentBridge (n : Nat) where
  RawState : Type
  RawStep : Type
  observedStep : RawStep
  coordinate : RawState → Fin n
  representative : Fin n → RawState
  coordinate_representative :
    ∀ i : Fin n, coordinate (representative i) = i
  stepTransform : RawStep → Fin n → Fin n
  stepTransform_injective :
    ∀ step : RawStep, Function.Injective (stepTransform step)

/-- Visible external R1 observation: terminal/prompt observations only. -/
def externalObs {n : Nat} (B : ExternalAlignmentBridge n) :
    AlignmentInterface → B.RawState → AlignmentObservation
  | AlignmentInterface.terminalOutputReader, _ =>
      AlignmentObservation.terminalOutput TerminalOutput.sameVisibleOutput
  | AlignmentInterface.promptClassReader, _ =>
      AlignmentObservation.promptClass PromptClass.samePromptClass

/-- External dynamic R2 target induced by the bridge coordinate. -/
def externalTarget {n : Nat} (B : ExternalAlignmentBridge n) :
    DynamicTarget B.RawState B.RawStep (Fin n) :=
  { targetAt := fun step state =>
      B.stepTransform step (B.coordinate state) }

/-- External mediator induced by the same causal trajectory coordinate. -/
def externalM {n : Nat} (B : ExternalAlignmentBridge n) :
    B.RawStep → B.RawState → Fin n :=
  fun step state => B.stepTransform step (B.coordinate state)

/-- The bridge contains a designated observed external step. -/
def external_observed_step
    {n : Nat} (B : ExternalAlignmentBridge n) :
    B.RawStep :=
  B.observedStep

/-- All external states are indistinguishable by the visible R1 interface. -/
theorem jointSame_externalStates
    {n : Nat} (B : ExternalAlignmentBridge n) (x y : B.RawState) :
    JointSame (externalObs B) I_alignment x y := by
  intro interface _hInterface
  cases interface <;> rfl

/-- All external states are indistinguishable by every visible subfamily. -/
theorem jointSame_externalStates_subfamily
    {n : Nat} (B : ExternalAlignmentBridge n)
    (K : Subfamily AlignmentInterface) (x y : B.RawState) :
    JointSame (externalObs B) K x y := by
  intro interface _hInterface
  cases interface <;> rfl

/-- First external representative state. -/
def externalX {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    B.RawState :=
  B.representative (firstTrajectory h)

/-- Second external representative state. -/
def externalY {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    B.RawState :=
  B.representative (secondTrajectory h)

/-- The external target separates the two canonical representatives. -/
theorem requiredAtStep_external
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n)
    (step : B.RawStep) :
    RequiredDistinction ((externalTarget B).targetAt step)
      (externalX B h) (externalY B h) := by
  intro hTarget
  have hCoord :
      B.coordinate (externalX B h) =
        B.coordinate (externalY B h) :=
    B.stepTransform_injective step hTarget
  unfold externalX externalY at hCoord
  rw [B.coordinate_representative (firstTrajectory h),
    B.coordinate_representative (secondTrajectory h)] at hCoord
  exact firstTrajectory_ne_secondTrajectory h hCoord

/-- The canonical external representatives form a dynamic R2 witness. -/
theorem dynamicDiagonalWitness_external
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n)
    (step : B.RawStep) :
    DynamicDiagonalizationWitness
      (externalObs B) (externalTarget B) I_alignment
      step (externalX B h) (externalY B h) := by
  exact
    ⟨requiredAtStep_external B h step,
      jointSame_externalStates B _ _⟩

/-- Every external step has a nonempty residual before mediation. -/
theorem dynamicResidualNonempty_external
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      DynamicResidualNonempty_R2
        (externalObs B) (externalTarget B) I_alignment step := by
  intro step
  exact
    ⟨externalX B h, externalY B h,
      dynamicDiagonalWitness_external B h step⟩

/-- The bridge mediator closes every external dynamic residual. -/
theorem dynamicMediatedResidualEmpty_externalM
    {n : Nat} (B : ExternalAlignmentBridge n) :
    ∀ step : B.RawStep,
      DynamicMediatedResidualEmpty
        (externalObs B) (externalTarget B) I_alignment
        step (externalM B step) := by
  intro step x y hResidual
  exact hResidual.1 hResidual.2.2

/-- The bridge mediator separates the external canonical pair. -/
theorem externalM_separates_canonical
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n)
    (step : B.RawStep) :
    externalM B step (externalX B h) ≠ externalM B step (externalY B h) := by
  exact requiredAtStep_external B h step

/-- Terminal-only does not recover the bridge mediator at any external step. -/
theorem no_descent_terminal_only_external
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      ¬ MediatorDescendsSubfamily
        (externalObs B) I_alignment_terminal_only (externalM B step) := by
  intro step hDescends
  exact externalM_separates_canonical B h step
    (hDescends (externalX B h) (externalY B h)
      (jointSame_externalStates_subfamily B I_alignment_terminal_only _ _))

/-- Prompt-only does not recover the bridge mediator at any external step. -/
theorem no_descent_prompt_only_external
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      ¬ MediatorDescendsSubfamily
        (externalObs B) I_alignment_prompt_only (externalM B step) := by
  intro step hDescends
  exact externalM_separates_canonical B h step
    (hDescends (externalX B h) (externalY B h)
      (jointSame_externalStates_subfamily B I_alignment_prompt_only _ _))

/-- Witness-style irreducibility of the bridge mediator. -/
theorem witnessedIrreducibleMediator_externalM
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      WitnessedIrreducibleMediator
        (externalObs B) I_alignment (externalM B step) := by
  intro step K _hProper
  exact
    ⟨externalX B h, externalY B h,
      jointSame_externalStates_subfamily B K _ _,
      externalM_separates_canonical B h step⟩

/-- Irreducibility of the bridge mediator. -/
theorem irreducibleMediator_externalM
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      IrreducibleMediator
        (externalObs B) I_alignment (externalM B step) := by
  intro step
  exact witnessedIrreducibleMediator_irreducibleMediator
    (externalObs B) I_alignment (externalM B step)
    (witnessedIrreducibleMediator_externalM B h step)

/-- Uniform proper mediated dynamic certificate transported by a bridge. -/
theorem uniformProperMediatedR2Certificate_externalM
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    UniformProperMediatedR2Certificate
      (externalObs B) (externalTarget B)
      I_alignment (externalM B) := by
  exact
    ⟨dynamicResidualNonempty_external B h,
      dynamicMediatedResidualEmpty_externalM B,
      irreducibleMediator_externalM B h⟩

/--
Any external mediated closure at a step induces an injection from `Fin n` into
the mediator codomain.
-/
theorem injective_of_mediatedResidualEmpty_external
    {n m : Nat} (B : ExternalAlignmentBridge n)
    (step : B.RawStep) {M : B.RawState → Fin m} :
    MediatedResidualEmpty
      (externalObs B) ((externalTarget B).targetAt step)
      I_alignment M →
      Function.Injective (fun i : Fin n => M (B.representative i)) := by
  intro hCloses i j hM
  by_cases hEq : i = j
  · exact hEq
  · have hReq :
        RequiredDistinction ((externalTarget B).targetAt step)
          (B.representative i) (B.representative j) := by
      intro hTarget
      have hCoord :
          B.coordinate (B.representative i) =
            B.coordinate (B.representative j) :=
        B.stepTransform_injective step hTarget
      rw [B.coordinate_representative i,
        B.coordinate_representative j] at hCoord
      exact hEq hCoord
    have hResidual :
        MediatedResidual
          (externalObs B) ((externalTarget B).targetAt step)
          I_alignment M
          (B.representative i) (B.representative j) :=
      ⟨hReq, ⟨jointSame_externalStates B _ _, hM⟩⟩
    exact False.elim (hCloses _ _ hResidual)

/-- No smaller proper mediated certificate can close a bridged external step. -/
theorem no_smaller_properMediatedR2Certificate_external_at_step
    {n : Nat} (B : ExternalAlignmentBridge n) :
    ∀ step : B.RawStep,
      ∀ m : Nat,
        m < n →
          ¬ ExistsProperMediatedR2CertificateAtDim
            (externalObs B) ((externalTarget B).targetAt step)
            I_alignment m := by
  intro step m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective (fun i : Fin n => M (B.representative i)) :=
    injective_of_mediatedResidualEmpty_external B step hCert.closes
  exact (FiniteDimensionHierarchy.no_injective_fin_of_lt n m hm
    (fun i : Fin n => M (B.representative i))) hInjective

/-- Dimension-minimal proper certificate for every bridged external step. -/
theorem dimensionMinimalProperMediatedR2Certificate_externalM_at_step
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      DimensionMinimalProperMediatedR2Certificate
        (externalObs B) ((externalTarget B).targetAt step)
        I_alignment (externalM B step) := by
  intro step
  exact
    ⟨⟨dynamicResidualNonempty_external B h step,
        dynamicMediatedResidualEmpty_externalM B step,
        irreducibleMediator_externalM B h step⟩,
      no_smaller_properMediatedR2Certificate_external_at_step B step⟩

/-- Exact proper mediated R2 dimension for every bridged external step. -/
theorem exactProperMediatedR2Dimension_n_external_at_step
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      ExactProperMediatedR2Dimension
        (externalObs B) ((externalTarget B).targetAt step)
        I_alignment n := by
  intro step
  exact exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_externalM_at_step B h step)

/-- Exact proper mediated dimension at the observed external step. -/
theorem exactProperMediatedR2Dimension_n_external_observedStep
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ExactProperMediatedR2Dimension
      (externalObs B) ((externalTarget B).targetAt B.observedStep)
      I_alignment n :=
  exactProperMediatedR2Dimension_n_external_at_step B h B.observedStep

/-- Dynamic exact proper mediated R2 dimension for every bridged step. -/
theorem dynamicExactProperMediatedR2Dimension_n_external_at_step
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ∀ step : B.RawStep,
      DynamicExactProperMediatedR2Dimension
        (externalObs B) (externalTarget B) I_alignment step n := by
  intro step
  exact exactProperMediatedR2Dimension_n_external_at_step B h step

/--
Observed-step external package: exact dimension at the designated step and
blocked descent to each visible marginal reader.
-/
theorem externallyAligned_observedStep_of_bridge
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ExactProperMediatedR2Dimension
        (externalObs B) ((externalTarget B).targetAt B.observedStep)
        I_alignment n
      ∧ ¬ MediatorDescendsSubfamily
          (externalObs B) I_alignment_terminal_only
          (externalM B B.observedStep)
      ∧ ¬ MediatorDescendsSubfamily
          (externalObs B) I_alignment_prompt_only
          (externalM B B.observedStep) := by
  exact
    ⟨exactProperMediatedR2Dimension_n_external_observedStep B h,
      no_descent_terminal_only_external B h B.observedStep,
      no_descent_prompt_only_external B h B.observedStep⟩

/--
External alignedness: an external carrier is aligned when the supplied bridge
closes the same dynamic R1/R2 residual with exact dimension `n`.
-/
def ExternallyAligned
    {n : Nat} (B : ExternalAlignmentBridge n) (_h : 1 < n) : Prop :=
  UniformProperMediatedR2Certificate
    (externalObs B) (externalTarget B) I_alignment (externalM B)
    ∧ (∀ step : B.RawStep,
        ExactProperMediatedR2Dimension
          (externalObs B) ((externalTarget B).targetAt step)
          I_alignment n)
    ∧ (∀ step : B.RawStep,
        ¬ MediatorDescendsSubfamily
          (externalObs B) I_alignment_terminal_only (externalM B step))
    ∧ (∀ step : B.RawStep,
        ¬ MediatorDescendsSubfamily
          (externalObs B) I_alignment_prompt_only (externalM B step))

/-- A bridge proves external alignedness exactly, not by assertion. -/
theorem externallyAligned_of_bridge
    {n : Nat} (B : ExternalAlignmentBridge n) (h : 1 < n) :
    ExternallyAligned B h := by
  exact
    ⟨uniformProperMediatedR2Certificate_externalM B h,
      exactProperMediatedR2Dimension_n_external_at_step B h,
      no_descent_terminal_only_external B h,
      no_descent_prompt_only_external B h⟩

/-- Final formal alignedness theorem for the dynamic R1/R2 carrier. -/
theorem endToEnd_aligned_alignment
    {n : Nat} (h : 1 < n) :
    Aligned h :=
  aligned_of_dynamicR1R2Certificate
    (dynamicAlignmentCertificate_alignment h)

/--
End-to-end dynamic package: uniform proper mediation, exact dimension at each
step, and non-descent to both visible marginal readers.
-/
theorem endToEnd_dynamic_alignment
    {n : Nat} (h : 1 < n) :
    UniformProperMediatedR2Certificate
      (obs_alignment (n := n)) (target_alignment (n := n))
      I_alignment (M_alignment (n := n))
      ∧ (∀ step : AlignmentStep n,
          ExactProperMediatedR2Dimension
            (obs_alignment (n := n)) (target_alignment.targetAt step)
            I_alignment n)
      ∧ (∀ step : AlignmentStep n,
          ¬ MediatorDescendsSubfamily
            (obs_alignment (n := n)) I_alignment_terminal_only
            (M_alignment step))
      ∧ (∀ step : AlignmentStep n,
          ¬ MediatorDescendsSubfamily
            (obs_alignment (n := n)) I_alignment_prompt_only
            (M_alignment step)) := by
  exact
    ⟨uniformProperMediatedR2Certificate_M_alignment h,
      exactProperMediatedR2Dimension_n_alignment_at_step h,
      no_descent_terminal_only_alignment h,
      no_descent_prompt_only_alignment h⟩

end LLMAlignmentDynamicR1R2
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.AlignmentStep
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.AlignmentState
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.AlignmentInterface
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.AlignmentObservation
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.obs_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.target_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.M_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicDiagonalWitness_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicResidualNonempty_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicMediatedResidualEmpty_M_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.uniformProperMediatedR2Certificate_M_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.no_descent_terminal_only_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.no_descent_prompt_only_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.exactProperMediatedR2Dimension_n_alignment_at_step
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicExactProperMediatedR2Dimension_n_alignment_at_step
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.compatDimEq_two_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.familyIrreducibleCompatibilityProfile_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicResidualProfile_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicResidualCoordinate_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.HasTransportableResidualProfile
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.Aligned
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.DynamicAlignmentCertificate
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.hasTransportableResidualProfile_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.aligned_of_dynamicR1R2Certificate
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicAlignmentCertificate_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.ExternalAlignmentBridge
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.externalObs
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.externalTarget
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.externalM
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.external_observed_step
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.uniformProperMediatedR2Certificate_externalM
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.exactProperMediatedR2Dimension_n_external_at_step
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.exactProperMediatedR2Dimension_n_external_observedStep
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.dynamicExactProperMediatedR2Dimension_n_external_at_step
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.externallyAligned_observedStep_of_bridge
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.ExternallyAligned
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.externallyAligned_of_bridge
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.endToEnd_aligned_alignment
#print axioms LocalSemanticClosure.LLMAlignmentDynamicR1R2.endToEnd_dynamic_alignment
/- AXIOM_AUDIT_END -/
