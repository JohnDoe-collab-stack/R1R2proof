import DynamicRegimesSelfContained
import PeanoPAFormulaAxioms

/-!
# Dynamic Peano PA formula-level R1/R2 certificates

This file is the dynamic companion of `PeanoPAFormulaAxioms.lean`.

It operates on the formula-level Peano objects:

* `PAFormulaAxiom`, whose main field is an actual first-order `Formula`;
* `PAFormulaComponent`, whose main field is also an actual first-order
  `Formula`, and which exposes the base/step components of induction.

The dynamic target is step-indexed.  For full axiom formulas, active steps
select the addition or multiplication recursive pair.  For formula components,
active steps select addition, multiplication, or the induction base/step pair
for a concrete formula parameter.

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace PeanoPAFormulaAxiomsDynamic

open Standalone.DynamicRegimesSelfContained


abbrev Term := PeanoPAFormulaAxioms.Term
abbrev Formula := PeanoPAFormulaAxioms.Formula
abbrev PAFormulaAxiom := PeanoPAFormulaAxioms.PAFormulaAxiom
abbrev PAFormulaComponent := PeanoPAFormulaAxioms.PAFormulaComponent
abbrev PAFormulaInterface := PeanoPAFormulaAxioms.PAFormulaInterface
abbrev PAFormulaTrace := PeanoPAFormulaAxioms.PAFormulaTrace
abbrev PAFormulaFamily := PeanoPAFormulaAxioms.PAFormulaFamily
abbrev Phase := PeanoPAFormulaAxioms.Phase

/-- The active R1 interface reads the formula trace. -/
def I_PA_formula_axiom : Subfamily PAFormulaInterface
  | PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace => True

/-- Observation map on full formula-level PA axioms. -/
def obs_PA_formula_axiom :
    PAFormulaInterface → PAFormulaAxiom → PAFormulaTrace
  | PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace, a => PeanoPAFormulaAxioms.traceOfPAFormulaAxiom a

/-- Stable formula-level target: read the base/step phase. -/
def sigma_PA_formula_axiom : PAFormulaAxiom → Phase :=
  PeanoPAFormulaAxioms.phaseOfPAFormulaAxiom

/-- Stable formula-level mediator. -/
def M_PA_formula_axiom : PAFormulaAxiom → Fin 2 :=
  fun a => PeanoPAFormulaAxioms.phaseToFin (sigma_PA_formula_axiom a)

/-- Canonical addition pair of actual PA axiom formulas. -/
def canonicalPair_PA_formula_axiom : PAFormulaAxiom × PAFormulaAxiom :=
  (PeanoPAFormulaAxioms.paAddZeroAxiom, PeanoPAFormulaAxioms.paAddSuccAxiom)

/-- The stable target separates the canonical addition formula pair. -/
theorem requiredAtCanonicalPair_PA_formula_axiom :
    RequiredDistinction sigma_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  change PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.Phase.step
  exact PeanoPAFormulaAxioms.Phase.base_ne_step

/-- R1 sees the same addition trace on the canonical formula pair. -/
theorem jointSameAtCanonicalPair_PA_formula_axiom :
    JointSame obs_PA_formula_axiom I_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  intro j _hj
  cases j
  rfl

/-- The canonical formula pair is a diagonalization witness. -/
theorem canonicalDiagonalWitness_PA_formula_axiom :
    DiagonalizationWitness
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 :=
  ⟨requiredAtCanonicalPair_PA_formula_axiom,
    jointSameAtCanonicalPair_PA_formula_axiom⟩

/-- The stable formula-level residual is nonempty. -/
theorem residualNonempty_PA_formula_axiom :
    ResidualNonempty_R2
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom :=
  ⟨canonicalPair_PA_formula_axiom.1,
    canonicalPair_PA_formula_axiom.2,
    canonicalDiagonalWitness_PA_formula_axiom⟩

/-- The stable formula-level mediator separates every diagonal witness. -/
theorem M_PA_formula_axiom_separates_witnesses :
    ∀ x y : PAFormulaAxiom,
      DiagonalizationWitness
        obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom x y →
        M_PA_formula_axiom x ≠ M_PA_formula_axiom y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_formula_axiom x = sigma_PA_formula_axiom y :=
    PeanoPAFormulaAxioms.phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The stable mediator closes the mediated residual. -/
theorem mediatedResidualEmpty_M_PA_formula_axiom :
    MediatedResidualEmpty
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom := by
  intro x y hResidual
  exact
    (M_PA_formula_axiom_separates_witnesses x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The stable mediator separates the canonical pair. -/
theorem M_PA_formula_axiom_separates_canonicalPair :
    M_PA_formula_axiom canonicalPair_PA_formula_axiom.1 ≠
      M_PA_formula_axiom canonicalPair_PA_formula_axiom.2 := by
  change PeanoPAFormulaAxioms.phaseToFin PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.phaseToFin PeanoPAFormulaAxioms.Phase.step
  exact PeanoPAFormulaAxioms.phaseToFin_base_ne_step

/-- A proper active subfamily omits the single formula-trace reader. -/
theorem not_mem_of_proper_formula_axiom_subfamily
    (K : Subfamily PAFormulaInterface) :
    Subfamily.Proper K I_PA_formula_axiom →
      ¬ K PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace := by
  intro hProper
  rcases hProper.2 with ⟨j, _hIj, hNotK⟩
  cases j
  exact hNotK

/-- The canonical pair is indistinguishable for every proper active subfamily. -/
theorem jointSameAtCanonicalPair_formula_axiom_of_properSubfamily
    (K : Subfamily PAFormulaInterface)
    (hProper : Subfamily.Proper K I_PA_formula_axiom) :
    JointSame obs_PA_formula_axiom K
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_formula_axiom_subfamily K hProper) hj)

/-- Explicit non-descent witness for every proper active subfamily. -/
theorem witnessedIrreducibleMediator_M_PA_formula_axiom :
    WitnessedIrreducibleMediator
      obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom := by
  intro K hProper
  exact
    ⟨canonicalPair_PA_formula_axiom.1,
      canonicalPair_PA_formula_axiom.2,
      jointSameAtCanonicalPair_formula_axiom_of_properSubfamily K hProper,
      M_PA_formula_axiom_separates_canonicalPair⟩

/-- The stable mediator is irreducible. -/
theorem irreducibleMediator_M_PA_formula_axiom :
    IrreducibleMediator
      obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom
    witnessedIrreducibleMediator_M_PA_formula_axiom

/-- Stable formula-level proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_PA_formula_axiom :
    ProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨residualNonempty_PA_formula_axiom,
    mediatedResidualEmpty_M_PA_formula_axiom,
    irreducibleMediator_M_PA_formula_axiom⟩

/-- Stable formula-level witnessed certificate. -/
theorem witnessedProperMediatedR2Certificate_M_PA_formula_axiom :
    WitnessedProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨residualNonempty_PA_formula_axiom,
    mediatedResidualEmpty_M_PA_formula_axiom,
    witnessedIrreducibleMediator_M_PA_formula_axiom⟩

/-- No smaller stable formula-level proper certificate exists below `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_formula_axiom :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Stable formula-level dimension-minimal certificate. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_formula_axiom :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨properMediatedR2Certificate_M_PA_formula_axiom,
    no_smaller_properMediatedR2Certificate_PA_formula_axiom⟩

/-- Stable formula-level exact proper dimension. -/
theorem exactProperMediatedR2Dimension_two_PA_formula_axiom :
    ExactProperMediatedR2Dimension
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_axiom

/-!
## Stable dynamic lift for full PA formula axioms
-/

/-- Stable dynamic step for full PA formula axioms. -/
inductive PAFormulaAxiomStableStep
  | formulaAxiom
deriving DecidableEq

/-- Stable dynamic target for full PA formula axioms. -/
def target_PA_formula_axiom_stable :
    DynamicTarget PAFormulaAxiom PAFormulaAxiomStableStep Phase :=
  { targetAt := fun _step => sigma_PA_formula_axiom }

/-- Stable step-indexed mediator for full PA formula axioms. -/
def M_PA_formula_axiom_stable :
    PAFormulaAxiomStableStep → PAFormulaAxiom → Fin 2 :=
  fun _step => M_PA_formula_axiom

/-- The canonical formula pair is a dynamic witness at the stable step. -/
theorem dynamicCanonicalDiagonalWitness_PA_formula_axiom_stable
    (step : PAFormulaAxiomStableStep) :
    DynamicDiagonalizationWitness
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom step
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  cases step
  exact canonicalDiagonalWitness_PA_formula_axiom

/-- The stable dynamic residual is nonempty. -/
theorem dynamicResidualNonempty_PA_formula_axiom_stable
    (step : PAFormulaAxiomStableStep) :
    DynamicResidualNonempty_R2
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom step := by
  cases step
  exact residualNonempty_PA_formula_axiom

/-- The stable dynamic mediator closes the mediated residual. -/
theorem dynamicMediatedResidualEmpty_M_PA_formula_axiom_stable
    (step : PAFormulaAxiomStableStep) :
    DynamicMediatedResidualEmpty
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom step (M_PA_formula_axiom_stable step) := by
  cases step
  exact mediatedResidualEmpty_M_PA_formula_axiom

/-- Uniform stable dynamic certificate for full PA formula axioms. -/
theorem uniformProperMediatedR2Certificate_M_PA_formula_axiom_stable :
    UniformProperMediatedR2Certificate
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom M_PA_formula_axiom_stable :=
  ⟨fun _step => residualNonempty_PA_formula_axiom,
    fun _step => mediatedResidualEmpty_M_PA_formula_axiom,
    fun _step => irreducibleMediator_M_PA_formula_axiom⟩

/-- Stable dynamic exact proper dimension. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_formula_axiom_stable
    (step : PAFormulaAxiomStableStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom step 2 := by
  cases step
  exact exactProperMediatedR2Dimension_two_PA_formula_axiom

/-- Stable formula-axiom dynamics rules out direct closure. -/
theorem not_dynamicClosed_R2_PA_formula_axiom_stable
    (step : PAFormulaAxiomStableStep) :
    ¬ DynamicClosed_R2
      obs_PA_formula_axiom target_PA_formula_axiom_stable
      I_PA_formula_axiom step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_formula_axiom target_PA_formula_axiom_stable
    I_PA_formula_axiom M_PA_formula_axiom_stable
    uniformProperMediatedR2Certificate_M_PA_formula_axiom_stable step

/-!
## Nontrivial dynamics for full PA formula axioms
-/

/-- Active dynamic step for full recursive PA axiom formulas. -/
inductive PAFormulaAxiomActiveStep
  | addition
  | multiplication
deriving DecidableEq

/-- Addition-active target on full PA axiom formulas. -/
def sigma_PA_formula_axiom_addition : PAFormulaAxiom → Phase
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.succ_ne_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.succ_injective⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.add_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.add_succ⟩ => PeanoPAFormulaAxioms.Phase.step
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.mul_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.mul_succ⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.induction _phi⟩ => PeanoPAFormulaAxioms.Phase.base

/-- Multiplication-active target on full PA axiom formulas. -/
def sigma_PA_formula_axiom_multiplication : PAFormulaAxiom → Phase
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.succ_ne_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.succ_injective⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.add_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.add_succ⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.mul_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.mul_succ⟩ => PeanoPAFormulaAxioms.Phase.step
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaAxiom.induction _phi⟩ => PeanoPAFormulaAxioms.Phase.base

/-- Step-dependent target on full PA axiom formulas. -/
def sigma_PA_formula_axiom_at :
    PAFormulaAxiomActiveStep → PAFormulaAxiom → Phase
  | PAFormulaAxiomActiveStep.addition => sigma_PA_formula_axiom_addition
  | PAFormulaAxiomActiveStep.multiplication =>
      sigma_PA_formula_axiom_multiplication

/-- Nontrivial dynamic target on full PA axiom formulas. -/
def target_PA_formula_axiom_active :
    DynamicTarget PAFormulaAxiom PAFormulaAxiomActiveStep Phase :=
  { targetAt := sigma_PA_formula_axiom_at }

/-- Step-dependent mediator on full PA axiom formulas. -/
def M_PA_formula_axiom_active :
    PAFormulaAxiomActiveStep → PAFormulaAxiom → Fin 2 :=
  fun step a => PeanoPAFormulaAxioms.phaseToFin (sigma_PA_formula_axiom_at step a)

/-- Active full-axiom formula pair at a dynamic step. -/
def activePair_PA_formula_axiom :
    PAFormulaAxiomActiveStep → PAFormulaAxiom × PAFormulaAxiom
  | PAFormulaAxiomActiveStep.addition =>
      (PeanoPAFormulaAxioms.paAddZeroAxiom, PeanoPAFormulaAxioms.paAddSuccAxiom)
  | PAFormulaAxiomActiveStep.multiplication =>
      (PeanoPAFormulaAxioms.paMulZeroAxiom, PeanoPAFormulaAxioms.paMulSuccAxiom)

/-- The active full-axiom target separates the active formula pair. -/
theorem requiredAtActivePair_PA_formula_axiom
    (step : PAFormulaAxiomActiveStep) :
    RequiredDistinction (target_PA_formula_axiom_active.targetAt step)
      (activePair_PA_formula_axiom step).1
      (activePair_PA_formula_axiom step).2 := by
  cases step <;>
    change PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.Phase.step <;>
    exact PeanoPAFormulaAxioms.Phase.base_ne_step

/-- R1 sees the same trace on the active full-axiom formula pair. -/
theorem jointSameAtActivePair_PA_formula_axiom
    (step : PAFormulaAxiomActiveStep) :
    JointSame obs_PA_formula_axiom I_PA_formula_axiom
      (activePair_PA_formula_axiom step).1
      (activePair_PA_formula_axiom step).2 := by
  intro j _hj
  cases j
  cases step <;> rfl

/-- The active full-axiom pair is a dynamic diagonal witness. -/
theorem dynamicCanonicalDiagonalWitness_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    DynamicDiagonalizationWitness
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step
      (activePair_PA_formula_axiom step).1
      (activePair_PA_formula_axiom step).2 :=
  ⟨requiredAtActivePair_PA_formula_axiom step,
    jointSameAtActivePair_PA_formula_axiom step⟩

/-- The active full-axiom dynamic residual is nonempty. -/
theorem dynamicResidualNonempty_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    DynamicResidualNonempty_R2
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step :=
  ⟨(activePair_PA_formula_axiom step).1,
    (activePair_PA_formula_axiom step).2,
    dynamicCanonicalDiagonalWitness_PA_formula_axiom_active step⟩

/-- The active full-axiom mediator separates every dynamic witness. -/
theorem M_PA_formula_axiom_active_separates_witnesses
    (step : PAFormulaAxiomActiveStep) :
    ∀ x y : PAFormulaAxiom,
      DynamicDiagonalizationWitness
        obs_PA_formula_axiom target_PA_formula_axiom_active
        I_PA_formula_axiom step x y →
        M_PA_formula_axiom_active step x ≠
          M_PA_formula_axiom_active step y := by
  intro x y hWitness hM
  have hPhase :
      target_PA_formula_axiom_active.targetAt step x =
        target_PA_formula_axiom_active.targetAt step y :=
    PeanoPAFormulaAxioms.phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The active full-axiom mediator closes each dynamic mediated residual. -/
theorem dynamicMediatedResidualEmpty_M_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    DynamicMediatedResidualEmpty
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step (M_PA_formula_axiom_active step) := by
  intro x y hResidual
  exact
    (M_PA_formula_axiom_active_separates_witnesses step x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The active full-axiom mediator separates the active pair. -/
theorem M_PA_formula_axiom_active_separates_pair
    (step : PAFormulaAxiomActiveStep) :
    M_PA_formula_axiom_active step (activePair_PA_formula_axiom step).1 ≠
      M_PA_formula_axiom_active step (activePair_PA_formula_axiom step).2 :=
  M_PA_formula_axiom_active_separates_witnesses step
    (activePair_PA_formula_axiom step).1
    (activePair_PA_formula_axiom step).2
    (dynamicCanonicalDiagonalWitness_PA_formula_axiom_active step)

/-- The active full-axiom pair is indistinguishable for proper subfamilies. -/
theorem jointSameAtActivePair_formula_axiom_of_properSubfamily
    (step : PAFormulaAxiomActiveStep)
    (K : Subfamily PAFormulaInterface)
    (hProper : Subfamily.Proper K I_PA_formula_axiom) :
    JointSame obs_PA_formula_axiom K
      (activePair_PA_formula_axiom step).1
      (activePair_PA_formula_axiom step).2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_formula_axiom_subfamily K hProper) hj)

/-- Explicit active full-axiom non-descent witnesses. -/
theorem witnessedIrreducibleMediator_M_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    WitnessedIrreducibleMediator
      obs_PA_formula_axiom I_PA_formula_axiom
      (M_PA_formula_axiom_active step) := by
  intro K hProper
  exact
    ⟨(activePair_PA_formula_axiom step).1,
      (activePair_PA_formula_axiom step).2,
      jointSameAtActivePair_formula_axiom_of_properSubfamily
        step K hProper,
      M_PA_formula_axiom_active_separates_pair step⟩

/-- Active full-axiom mediator irreducibility. -/
theorem irreducibleMediator_M_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    IrreducibleMediator
      obs_PA_formula_axiom I_PA_formula_axiom
      (M_PA_formula_axiom_active step) :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_axiom I_PA_formula_axiom
    (M_PA_formula_axiom_active step)
    (witnessedIrreducibleMediator_M_PA_formula_axiom_active step)

/-- Uniform proper certificate for active full-axiom dynamics. -/
theorem uniformProperMediatedR2Certificate_M_PA_formula_axiom_active :
    UniformProperMediatedR2Certificate
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom M_PA_formula_axiom_active :=
  ⟨dynamicResidualNonempty_PA_formula_axiom_active,
    dynamicMediatedResidualEmpty_M_PA_formula_axiom_active,
    irreducibleMediator_M_PA_formula_axiom_active⟩

/-- Stepwise active full-axiom certificate. -/
theorem stepwiseProperMediatedR2Certificate_M_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    StepwiseProperMediatedR2Certificate
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step (M_PA_formula_axiom_active step) :=
  stepwiseProperMediatedR2Certificate_of_uniform
    uniformProperMediatedR2Certificate_M_PA_formula_axiom_active step

/-- Stepwise witnessed active full-axiom certificate. -/
theorem stepwiseWitnessedProperMediatedR2Certificate_M_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    StepwiseWitnessedProperMediatedR2Certificate
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step (M_PA_formula_axiom_active step) :=
  ⟨dynamicResidualNonempty_PA_formula_axiom_active step,
    dynamicMediatedResidualEmpty_M_PA_formula_axiom_active step,
    witnessedIrreducibleMediator_M_PA_formula_axiom_active step⟩

/-- No smaller active full-axiom certificate exists below `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_formula_axiom
          (target_PA_formula_axiom_active.targetAt step)
          I_PA_formula_axiom m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_formula_axiom
        (target_PA_formula_axiom_active.targetAt step)
        I_PA_formula_axiom
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_formula_axiom
            (target_PA_formula_axiom_active.targetAt step)
            I_PA_formula_axiom
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Exact proper dimension for active full-axiom dynamics. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    ⟨stepwiseProperMediatedR2Certificate_M_PA_formula_axiom_active step,
      no_smaller_properMediatedR2Certificate_PA_formula_axiom_active step⟩

/-- Active full-axiom dynamics rules out direct dynamic closure. -/
theorem not_dynamicClosed_R2_PA_formula_axiom_active
    (step : PAFormulaAxiomActiveStep) :
    ¬ DynamicClosed_R2
      obs_PA_formula_axiom target_PA_formula_axiom_active
      I_PA_formula_axiom step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_formula_axiom target_PA_formula_axiom_active
    I_PA_formula_axiom M_PA_formula_axiom_active
    uniformProperMediatedR2Certificate_M_PA_formula_axiom_active step

/-!
## Formula-component dynamics, including induction
-/

/-- Active R1 interface for formula components. -/
def I_PA_formula_component : Subfamily PAFormulaInterface
  | PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace => True

/-- Observation map on formula-level PA components. -/
def obs_PA_formula_component :
    PAFormulaInterface → PAFormulaComponent → PAFormulaTrace
  | PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace, c => PeanoPAFormulaAxioms.traceOfPAFormulaComponent c

/-- Stable target on PA formula components. -/
def sigma_PA_formula_component : PAFormulaComponent → Phase :=
  PeanoPAFormulaAxioms.phaseOfPAFormulaComponent

/-- Stable component mediator. -/
def M_PA_formula_component : PAFormulaComponent → Fin 2 :=
  fun c => PeanoPAFormulaAxioms.phaseToFin (sigma_PA_formula_component c)

/-- Canonical component pair for induction at `phi0`. -/
def canonicalPair_PA_formula_component :
    PAFormulaComponent × PAFormulaComponent :=
  (PeanoPAFormulaAxioms.x_pa_induction_base, PeanoPAFormulaAxioms.y_pa_induction_step)

/-- Stable target separates the canonical induction component pair. -/
theorem requiredAtCanonicalPair_PA_formula_component :
    RequiredDistinction sigma_PA_formula_component
      canonicalPair_PA_formula_component.1
      canonicalPair_PA_formula_component.2 := by
  change PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.Phase.step
  exact PeanoPAFormulaAxioms.Phase.base_ne_step

/-- R1 sees the same induction trace on the canonical component pair. -/
theorem jointSameAtCanonicalPair_PA_formula_component :
    JointSame obs_PA_formula_component I_PA_formula_component
      canonicalPair_PA_formula_component.1
      canonicalPair_PA_formula_component.2 := by
  intro j _hj
  cases j
  rfl

/-- Stable component diagonal witness. -/
theorem canonicalDiagonalWitness_PA_formula_component :
    DiagonalizationWitness
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component
      canonicalPair_PA_formula_component.1
      canonicalPair_PA_formula_component.2 :=
  ⟨requiredAtCanonicalPair_PA_formula_component,
    jointSameAtCanonicalPair_PA_formula_component⟩

/-- Stable component residual nonemptiness. -/
theorem residualNonempty_PA_formula_component :
    ResidualNonempty_R2
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component :=
  ⟨canonicalPair_PA_formula_component.1,
    canonicalPair_PA_formula_component.2,
    canonicalDiagonalWitness_PA_formula_component⟩

/-- Stable component mediator separates every residual witness. -/
theorem M_PA_formula_component_separates_witnesses :
    ∀ x y : PAFormulaComponent,
      DiagonalizationWitness
        obs_PA_formula_component sigma_PA_formula_component
        I_PA_formula_component x y →
        M_PA_formula_component x ≠ M_PA_formula_component y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_formula_component x = sigma_PA_formula_component y :=
    PeanoPAFormulaAxioms.phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- Stable component mediated closure. -/
theorem mediatedResidualEmpty_M_PA_formula_component :
    MediatedResidualEmpty
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component := by
  intro x y hResidual
  exact
    (M_PA_formula_component_separates_witnesses x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- Stable component mediator separates the canonical pair. -/
theorem M_PA_formula_component_separates_canonicalPair :
    M_PA_formula_component canonicalPair_PA_formula_component.1 ≠
      M_PA_formula_component canonicalPair_PA_formula_component.2 := by
  change PeanoPAFormulaAxioms.phaseToFin PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.phaseToFin PeanoPAFormulaAxioms.Phase.step
  exact PeanoPAFormulaAxioms.phaseToFin_base_ne_step

/-- A proper component subfamily omits the single formula-trace reader. -/
theorem not_mem_of_proper_formula_component_subfamily
    (K : Subfamily PAFormulaInterface) :
    Subfamily.Proper K I_PA_formula_component →
      ¬ K PeanoPAFormulaAxioms.PAFormulaInterface.formulaTrace := by
  intro hProper
  rcases hProper.2 with ⟨j, _hIj, hNotK⟩
  cases j
  exact hNotK

/-- Canonical component pair indistinguishable for proper subfamilies. -/
theorem jointSameAtCanonicalPair_formula_component_of_properSubfamily
    (K : Subfamily PAFormulaInterface)
    (hProper : Subfamily.Proper K I_PA_formula_component) :
    JointSame obs_PA_formula_component K
      canonicalPair_PA_formula_component.1
      canonicalPair_PA_formula_component.2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_formula_component_subfamily K hProper) hj)

/-- Stable component witnessed irreducibility. -/
theorem witnessedIrreducibleMediator_M_PA_formula_component :
    WitnessedIrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      M_PA_formula_component := by
  intro K hProper
  exact
    ⟨canonicalPair_PA_formula_component.1,
      canonicalPair_PA_formula_component.2,
      jointSameAtCanonicalPair_formula_component_of_properSubfamily
        K hProper,
      M_PA_formula_component_separates_canonicalPair⟩

/-- Stable component irreducibility. -/
theorem irreducibleMediator_M_PA_formula_component :
    IrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      M_PA_formula_component :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_component I_PA_formula_component M_PA_formula_component
    witnessedIrreducibleMediator_M_PA_formula_component

/-- Stable component proper certificate. -/
theorem properMediatedR2Certificate_M_PA_formula_component :
    ProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨residualNonempty_PA_formula_component,
    mediatedResidualEmpty_M_PA_formula_component,
    irreducibleMediator_M_PA_formula_component⟩

/-- Stable component witnessed proper certificate. -/
theorem witnessedProperMediatedR2Certificate_M_PA_formula_component :
    WitnessedProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨residualNonempty_PA_formula_component,
    mediatedResidualEmpty_M_PA_formula_component,
    witnessedIrreducibleMediator_M_PA_formula_component⟩

/-- No smaller stable component certificate exists below `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_formula_component :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_formula_component sigma_PA_formula_component
          I_PA_formula_component m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_formula_component sigma_PA_formula_component
        I_PA_formula_component
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_formula_component sigma_PA_formula_component
            I_PA_formula_component
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Stable component dimension-minimal certificate. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_formula_component :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨properMediatedR2Certificate_M_PA_formula_component,
    no_smaller_properMediatedR2Certificate_PA_formula_component⟩

/-- Stable component exact dimension. -/
theorem exactProperMediatedR2Dimension_two_PA_formula_component :
    ExactProperMediatedR2Dimension
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_component

/-- Dynamic step selecting an active PA formula component pair. -/
inductive PAFormulaComponentActiveStep
  | addition
  | multiplication
  | induction (phi : Formula)
deriving DecidableEq

/-- Return `selectedPhase` exactly when the formula parameter is selected. -/
def phaseIfFormulaSelected
    (selected actual : Formula) (selectedPhase : Phase) : Phase :=
  match (inferInstance : Decidable (actual = selected)) with
  | isTrue _ => selectedPhase
  | isFalse _ => PeanoPAFormulaAxioms.Phase.base

/-- Selection by the same formula returns the selected phase. -/
theorem phaseIfFormulaSelected_self
    (phi : Formula) (selectedPhase : Phase) :
    phaseIfFormulaSelected phi phi selectedPhase = selectedPhase := by
  unfold phaseIfFormulaSelected
  cases (inferInstance : Decidable (phi = phi)) with
  | isTrue _h =>
      rfl
  | isFalse hNe =>
      exact False.elim (hNe rfl)

/-- Addition-active target on formula components. -/
def sigma_PA_formula_component_addition : PAFormulaComponent → Phase
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_ne_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_injective⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_step⟩ => PeanoPAFormulaAxioms.Phase.step
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_step⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_base _phi⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_step _phi⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_full _phi⟩ => PeanoPAFormulaAxioms.Phase.base

/-- Multiplication-active target on formula components. -/
def sigma_PA_formula_component_multiplication : PAFormulaComponent → Phase
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_ne_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_injective⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_step⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_step⟩ => PeanoPAFormulaAxioms.Phase.step
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_base _phi⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_step _phi⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_full _phi⟩ => PeanoPAFormulaAxioms.Phase.base

/-- Induction-active target on formula components for the selected formula. -/
def sigma_PA_formula_component_induction
    (selected : Formula) : PAFormulaComponent → Phase
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_ne_zero⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.succ_injective⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_step⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_base⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_step⟩ => PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_base actual⟩ =>
      phaseIfFormulaSelected selected actual PeanoPAFormulaAxioms.Phase.base
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_step actual⟩ =>
      phaseIfFormulaSelected selected actual PeanoPAFormulaAxioms.Phase.step
  | ⟨_, PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_full _actual⟩ => PeanoPAFormulaAxioms.Phase.base

/-- Step-dependent target on formula components. -/
def sigma_PA_formula_component_at :
    PAFormulaComponentActiveStep → PAFormulaComponent → Phase
  | PAFormulaComponentActiveStep.addition =>
      sigma_PA_formula_component_addition
  | PAFormulaComponentActiveStep.multiplication =>
      sigma_PA_formula_component_multiplication
  | PAFormulaComponentActiveStep.induction phi =>
      sigma_PA_formula_component_induction phi

/-- Nontrivial dynamic target on PA formula components. -/
def target_PA_formula_component_active :
    DynamicTarget PAFormulaComponent PAFormulaComponentActiveStep Phase :=
  { targetAt := sigma_PA_formula_component_at }

/-- Step-dependent mediator on PA formula components. -/
def M_PA_formula_component_active :
    PAFormulaComponentActiveStep → PAFormulaComponent → Fin 2 :=
  fun step c => PeanoPAFormulaAxioms.phaseToFin (sigma_PA_formula_component_at step c)

/-- Active formula-component pair for each dynamic step. -/
def activePair_PA_formula_component :
    PAFormulaComponentActiveStep → PAFormulaComponent × PAFormulaComponent
  | PAFormulaComponentActiveStep.addition =>
      (⟨PeanoPAFormulaAxioms.paAddZeroFormula, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_base⟩,
        ⟨PeanoPAFormulaAxioms.paAddSuccFormula, PeanoPAFormulaAxioms.IsPAFormulaComponent.add_step⟩)
  | PAFormulaComponentActiveStep.multiplication =>
      (⟨PeanoPAFormulaAxioms.paMulZeroFormula, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_base⟩,
        ⟨PeanoPAFormulaAxioms.paMulSuccFormula, PeanoPAFormulaAxioms.IsPAFormulaComponent.mul_step⟩)
  | PAFormulaComponentActiveStep.induction phi =>
      (⟨PeanoPAFormulaAxioms.inductionBaseFormula phi,
          PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_base phi⟩,
        ⟨PeanoPAFormulaAxioms.inductionStepFormula phi,
          PeanoPAFormulaAxioms.IsPAFormulaComponent.induction_step phi⟩)

/-- The active component target separates the active formula pair. -/
theorem requiredAtActivePair_PA_formula_component
    (step : PAFormulaComponentActiveStep) :
    RequiredDistinction (target_PA_formula_component_active.targetAt step)
      (activePair_PA_formula_component step).1
      (activePair_PA_formula_component step).2 := by
  cases step with
  | addition =>
      change PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.Phase.step
      exact PeanoPAFormulaAxioms.Phase.base_ne_step
  | multiplication =>
      change PeanoPAFormulaAxioms.Phase.base ≠ PeanoPAFormulaAxioms.Phase.step
      exact PeanoPAFormulaAxioms.Phase.base_ne_step
  | induction phi =>
      change
        phaseIfFormulaSelected phi phi PeanoPAFormulaAxioms.Phase.base ≠
          phaseIfFormulaSelected phi phi PeanoPAFormulaAxioms.Phase.step
      rw [phaseIfFormulaSelected_self, phaseIfFormulaSelected_self]
      exact PeanoPAFormulaAxioms.Phase.base_ne_step

/-- R1 sees the same trace on the active formula-component pair. -/
theorem jointSameAtActivePair_PA_formula_component
    (step : PAFormulaComponentActiveStep) :
    JointSame obs_PA_formula_component I_PA_formula_component
      (activePair_PA_formula_component step).1
      (activePair_PA_formula_component step).2 := by
  intro j _hj
  cases j
  cases step <;> rfl

/-- The active formula-component pair is a dynamic diagonal witness. -/
theorem dynamicCanonicalDiagonalWitness_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    DynamicDiagonalizationWitness
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step
      (activePair_PA_formula_component step).1
      (activePair_PA_formula_component step).2 :=
  ⟨requiredAtActivePair_PA_formula_component step,
    jointSameAtActivePair_PA_formula_component step⟩

/-- The active formula-component dynamic residual is nonempty. -/
theorem dynamicResidualNonempty_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    DynamicResidualNonempty_R2
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step :=
  ⟨(activePair_PA_formula_component step).1,
    (activePair_PA_formula_component step).2,
    dynamicCanonicalDiagonalWitness_PA_formula_component_active step⟩

/-- The active component mediator separates every dynamic witness. -/
theorem M_PA_formula_component_active_separates_witnesses
    (step : PAFormulaComponentActiveStep) :
    ∀ x y : PAFormulaComponent,
      DynamicDiagonalizationWitness
        obs_PA_formula_component target_PA_formula_component_active
        I_PA_formula_component step x y →
        M_PA_formula_component_active step x ≠
          M_PA_formula_component_active step y := by
  intro x y hWitness hM
  have hPhase :
      target_PA_formula_component_active.targetAt step x =
        target_PA_formula_component_active.targetAt step y :=
    PeanoPAFormulaAxioms.phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The active component mediator closes each dynamic mediated residual. -/
theorem dynamicMediatedResidualEmpty_M_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    DynamicMediatedResidualEmpty
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step (M_PA_formula_component_active step) := by
  intro x y hResidual
  exact
    (M_PA_formula_component_active_separates_witnesses step x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The active component mediator separates the active pair. -/
theorem M_PA_formula_component_active_separates_pair
    (step : PAFormulaComponentActiveStep) :
    M_PA_formula_component_active step
        (activePair_PA_formula_component step).1 ≠
      M_PA_formula_component_active step
        (activePair_PA_formula_component step).2 :=
  M_PA_formula_component_active_separates_witnesses step
    (activePair_PA_formula_component step).1
    (activePair_PA_formula_component step).2
    (dynamicCanonicalDiagonalWitness_PA_formula_component_active step)

/-- The active component pair is indistinguishable for proper subfamilies. -/
theorem jointSameAtActivePair_formula_component_of_properSubfamily
    (step : PAFormulaComponentActiveStep)
    (K : Subfamily PAFormulaInterface)
    (hProper : Subfamily.Proper K I_PA_formula_component) :
    JointSame obs_PA_formula_component K
      (activePair_PA_formula_component step).1
      (activePair_PA_formula_component step).2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_formula_component_subfamily K hProper) hj)

/-- Explicit active component non-descent witnesses. -/
theorem witnessedIrreducibleMediator_M_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    WitnessedIrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      (M_PA_formula_component_active step) := by
  intro K hProper
  exact
    ⟨(activePair_PA_formula_component step).1,
      (activePair_PA_formula_component step).2,
      jointSameAtActivePair_formula_component_of_properSubfamily
        step K hProper,
      M_PA_formula_component_active_separates_pair step⟩

/-- Active component mediator irreducibility. -/
theorem irreducibleMediator_M_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    IrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      (M_PA_formula_component_active step) :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_component I_PA_formula_component
    (M_PA_formula_component_active step)
    (witnessedIrreducibleMediator_M_PA_formula_component_active step)

/-- Uniform proper certificate for active component dynamics. -/
theorem uniformProperMediatedR2Certificate_M_PA_formula_component_active :
    UniformProperMediatedR2Certificate
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component M_PA_formula_component_active :=
  ⟨dynamicResidualNonempty_PA_formula_component_active,
    dynamicMediatedResidualEmpty_M_PA_formula_component_active,
    irreducibleMediator_M_PA_formula_component_active⟩

/-- Stepwise active component proper certificate. -/
theorem stepwiseProperMediatedR2Certificate_M_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    StepwiseProperMediatedR2Certificate
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step (M_PA_formula_component_active step) :=
  stepwiseProperMediatedR2Certificate_of_uniform
    uniformProperMediatedR2Certificate_M_PA_formula_component_active step

/-- Stepwise active component witnessed certificate. -/
theorem stepwiseWitnessedProperMediatedR2Certificate_M_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    StepwiseWitnessedProperMediatedR2Certificate
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step (M_PA_formula_component_active step) :=
  ⟨dynamicResidualNonempty_PA_formula_component_active step,
    dynamicMediatedResidualEmpty_M_PA_formula_component_active step,
    witnessedIrreducibleMediator_M_PA_formula_component_active step⟩

/-- No smaller active component certificate exists below `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_formula_component
          (target_PA_formula_component_active.targetAt step)
          I_PA_formula_component m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_formula_component
        (target_PA_formula_component_active.targetAt step)
        I_PA_formula_component
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_formula_component
            (target_PA_formula_component_active.targetAt step)
            I_PA_formula_component
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Exact proper dimension for active component dynamics, including induction. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    ⟨stepwiseProperMediatedR2Certificate_M_PA_formula_component_active step,
      no_smaller_properMediatedR2Certificate_PA_formula_component_active step⟩

/-- Active formula-component dynamics rules out direct dynamic closure. -/
theorem not_dynamicClosed_R2_PA_formula_component_active
    (step : PAFormulaComponentActiveStep) :
    ¬ DynamicClosed_R2
      obs_PA_formula_component target_PA_formula_component_active
      I_PA_formula_component step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_formula_component target_PA_formula_component_active
    I_PA_formula_component M_PA_formula_component_active
    uniformProperMediatedR2Certificate_M_PA_formula_component_active step

end PeanoPAFormulaAxiomsDynamic
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.target_PA_formula_axiom_stable
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.uniformProperMediatedR2Certificate_M_PA_formula_axiom_stable
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.dynamicExactProperMediatedR2Dimension_two_PA_formula_axiom_stable
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.PAFormulaAxiomActiveStep
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.target_PA_formula_axiom_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.activePair_PA_formula_axiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.dynamicCanonicalDiagonalWitness_PA_formula_axiom_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.uniformProperMediatedR2Certificate_M_PA_formula_axiom_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.dynamicExactProperMediatedR2Dimension_two_PA_formula_axiom_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.PAFormulaComponentActiveStep
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.phaseIfFormulaSelected
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.target_PA_formula_component_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.activePair_PA_formula_component
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.dynamicCanonicalDiagonalWitness_PA_formula_component_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.uniformProperMediatedR2Certificate_M_PA_formula_component_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.dynamicExactProperMediatedR2Dimension_two_PA_formula_component_active
#print axioms LocalSemanticClosure.PeanoPAFormulaAxiomsDynamic.not_dynamicClosed_R2_PA_formula_component_active
/- AXIOM_AUDIT_END -/
