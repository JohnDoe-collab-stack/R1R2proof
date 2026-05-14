import DynamicRegimesSelfContained

/-!
# Dynamic Peano axiom-level R1/R2 certificate

This file instantiates the standalone R1/R2 certificate directly on the finite
recursive Peano axiom fragment:

* `add_zero`;
* `add_succ`;
* `mul_zero`;
* `mul_succ`.

It does not assume Peano arithmetic as Lean axioms.  The Peano recursion
axioms are the formal objects on which the existing R1/R2 machinery operates.
-/

namespace LocalSemanticClosure
namespace PeanoAxiomLevelDynamic

open Standalone.DynamicRegimesSelfContained

/-- The finite recursive Peano axiom fragment. -/
inductive PARecAxiom
  | add_zero
  | add_succ
  | mul_zero
  | mul_succ
deriving DecidableEq

/-- The marginal interface: read only the recursive family. -/
inductive PARecInterface
  | recursionFamily
deriving DecidableEq

/-- Recursive family of a Peano recursion axiom. -/
inductive RecFamily
  | addition
  | multiplication
deriving DecidableEq

/-- Base/step phase of a recursive axiom. -/
inductive Phase
  | base
  | step
deriving DecidableEq

namespace Phase

/-- The base phase is distinct from the step phase. -/
theorem base_ne_step : Phase.base ≠ Phase.step := by
  intro h
  cases h

end Phase

/-- The active R1 interface family reads only the recursion family. -/
def I_PA_axiom : Subfamily PARecInterface
  | PARecInterface.recursionFamily => True

/-- Observation map: the R1 reading forgets base/step and keeps only family. -/
def obs_PA_axiom : PARecInterface → PARecAxiom → RecFamily
  | PARecInterface.recursionFamily, PARecAxiom.add_zero => RecFamily.addition
  | PARecInterface.recursionFamily, PARecAxiom.add_succ => RecFamily.addition
  | PARecInterface.recursionFamily, PARecAxiom.mul_zero => RecFamily.multiplication
  | PARecInterface.recursionFamily, PARecAxiom.mul_succ => RecFamily.multiplication

/-- Target map: read the base/step phase. -/
def sigma_PA_axiom : PARecAxiom → Phase
  | PARecAxiom.add_zero => Phase.base
  | PARecAxiom.add_succ => Phase.step
  | PARecAxiom.mul_zero => Phase.base
  | PARecAxiom.mul_succ => Phase.step

/-- Encode the phase as the finite two-point mediator. -/
def phaseToFin : Phase → Fin 2
  | Phase.base => ⟨0, by decide⟩
  | Phase.step => ⟨1, by decide⟩

/-- The two finite phase values are distinct. -/
theorem phaseToFin_base_ne_step :
    phaseToFin Phase.base ≠ phaseToFin Phase.step := by
  decide

/-- The finite phase encoding is injective. -/
theorem phaseToFin_injective :
    Function.Injective phaseToFin := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (phaseToFin_base_ne_step h)
  · exact False.elim (phaseToFin_base_ne_step h.symm)
  · rfl

/-- R2 mediator: the finite base/step readout. -/
def M_PA_axiom : PARecAxiom → Fin 2 :=
  fun a => phaseToFin (sigma_PA_axiom a)

/-- Canonical base axiom in the addition recursion pair. -/
def x_add_zero : PARecAxiom := PARecAxiom.add_zero

/-- Canonical step axiom in the addition recursion pair. -/
def y_add_succ : PARecAxiom := PARecAxiom.add_succ

/-- The canonical addition pair. -/
def canonicalPair_PA_axiom : PARecAxiom × PARecAxiom :=
  (x_add_zero, y_add_succ)

/-- The target separates `add_zero` from `add_succ`. -/
theorem requiredAtCanonicalPair_PA_axiom :
    RequiredDistinction sigma_PA_axiom
      canonicalPair_PA_axiom.1 canonicalPair_PA_axiom.2 := by
  exact Phase.base_ne_step

/-- The active R1 interface sees the same recursion family on the canonical pair. -/
theorem jointSameAtCanonicalPair_PA_axiom :
    JointSame obs_PA_axiom I_PA_axiom
      canonicalPair_PA_axiom.1 canonicalPair_PA_axiom.2 := by
  intro j _hj
  cases j
  rfl

/-- The canonical pair is a diagonalization witness at the axiom level. -/
theorem canonicalDiagonalWitness_PA_axiom :
    DiagonalizationWitness obs_PA_axiom sigma_PA_axiom I_PA_axiom
      canonicalPair_PA_axiom.1 canonicalPair_PA_axiom.2 :=
  ⟨requiredAtCanonicalPair_PA_axiom, jointSameAtCanonicalPair_PA_axiom⟩

/-- The residual is nonempty at the R1 axiom level. -/
theorem residualNonempty_PA_axiom :
    ResidualNonempty_R2 obs_PA_axiom sigma_PA_axiom I_PA_axiom :=
  ⟨canonicalPair_PA_axiom.1,
    canonicalPair_PA_axiom.2,
    canonicalDiagonalWitness_PA_axiom⟩

/-- The phase mediator separates every axiom-level diagonal witness. -/
theorem M_PA_axiom_separates_witnesses :
    ∀ x y : PARecAxiom,
      DiagonalizationWitness obs_PA_axiom sigma_PA_axiom I_PA_axiom x y →
        M_PA_axiom x ≠ M_PA_axiom y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_axiom x = sigma_PA_axiom y :=
    phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The phase mediator closes the axiom-level mediated residual. -/
theorem mediatedResidualEmpty_M_PA_axiom :
    MediatedResidualEmpty obs_PA_axiom sigma_PA_axiom I_PA_axiom
      M_PA_axiom := by
  intro x y hResidual
  exact (M_PA_axiom_separates_witnesses x y ⟨hResidual.1, hResidual.2.1⟩)
    hResidual.2.2

/-- The phase mediator separates the canonical pair. -/
theorem M_PA_axiom_separates_canonicalPair :
    M_PA_axiom canonicalPair_PA_axiom.1 ≠
      M_PA_axiom canonicalPair_PA_axiom.2 :=
  phaseToFin_base_ne_step

/-- Any proper active subfamily omits the single active recursion-family reader. -/
theorem not_mem_of_proper_subfamily
    (K : Subfamily PARecInterface) :
    Subfamily.Proper K I_PA_axiom →
      ¬ K PARecInterface.recursionFamily := by
  intro hProper
  rcases hProper.2 with ⟨j, _hIj, hNotK⟩
  cases j
  exact hNotK

/-- The canonical pair is indistinguishable for every proper active subfamily. -/
theorem jointSameAtCanonicalPair_of_properSubfamily
    (K : Subfamily PARecInterface)
    (hProper : Subfamily.Proper K I_PA_axiom) :
    JointSame obs_PA_axiom K
      canonicalPair_PA_axiom.1 canonicalPair_PA_axiom.2 := by
  intro j hj
  cases j
  exact False.elim ((not_mem_of_proper_subfamily K hProper) hj)

/-- Explicit non-descent witness for every proper active subfamily. -/
theorem witnessedIrreducibleMediator_M_PA_axiom :
    WitnessedIrreducibleMediator obs_PA_axiom I_PA_axiom M_PA_axiom := by
  intro K hProper
  exact
    ⟨canonicalPair_PA_axiom.1,
      canonicalPair_PA_axiom.2,
      jointSameAtCanonicalPair_of_properSubfamily K hProper,
      M_PA_axiom_separates_canonicalPair⟩

/-- The phase mediator does not descend to any proper active subfamily. -/
theorem irreducibleMediator_M_PA_axiom :
    IrreducibleMediator obs_PA_axiom I_PA_axiom M_PA_axiom :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_axiom I_PA_axiom M_PA_axiom
    witnessedIrreducibleMediator_M_PA_axiom

/-- The axiom-level mediator gives a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_PA_axiom :
    ProperMediatedR2Certificate
      obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom :=
  ⟨residualNonempty_PA_axiom,
    mediatedResidualEmpty_M_PA_axiom,
    irreducibleMediator_M_PA_axiom⟩

/-- The axiom-level mediator gives a witnessed proper mediated R2 certificate. -/
theorem witnessedProperMediatedR2Certificate_M_PA_axiom :
    WitnessedProperMediatedR2Certificate
      obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom :=
  ⟨residualNonempty_PA_axiom,
    mediatedResidualEmpty_M_PA_axiom,
    witnessedIrreducibleMediator_M_PA_axiom⟩

/-- No smaller proper mediated certificate exists below dimension `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_axiom :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_axiom sigma_PA_axiom I_PA_axiom m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_axiom sigma_PA_axiom I_PA_axiom
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_axiom sigma_PA_axiom I_PA_axiom
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- The axiom-level mediator realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_axiom :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom :=
  ⟨properMediatedR2Certificate_M_PA_axiom,
    no_smaller_properMediatedR2Certificate_PA_axiom⟩

/--
The axiom-level mediator realizes dimension-minimal witnessed proper R2
closure.
-/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_axiom :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom :=
  ⟨witnessedProperMediatedR2Certificate_M_PA_axiom,
    no_smaller_properMediatedR2Certificate_PA_axiom⟩

/-- The exact proper mediated R2 dimension of the axiom-level certificate is `2`. -/
theorem exactProperMediatedR2Dimension_two_PA_axiom :
    ExactProperMediatedR2Dimension
      obs_PA_axiom sigma_PA_axiom I_PA_axiom 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_axiom

/-- End-to-end extraction of the Peano axiom-level certificate package. -/
theorem endToEnd_PA_axiom :
    ResidualNonempty_R2 obs_PA_axiom sigma_PA_axiom I_PA_axiom
      ∧ MediatedResidualEmpty
          obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom
      ∧ IrreducibleMediator obs_PA_axiom I_PA_axiom M_PA_axiom
      ∧ (∀ m : Nat,
          m < 2 →
            ¬ ExistsProperMediatedR2CertificateAtDim
              obs_PA_axiom sigma_PA_axiom I_PA_axiom m) :=
  endToEnd_staticProperMediatedR2Certificate
    obs_PA_axiom sigma_PA_axiom I_PA_axiom M_PA_axiom
    dimensionMinimalProperMediatedR2Certificate_M_PA_axiom

/-
The next block extends the same axiom-level certificate from the finite
recursive fragment to explicit Peano axiom components.  This is the intended
substrate for induction: an induction instance contributes a base component and
a step component with the same formula parameter.
-/

/-- A minimal code-level placeholder for one-variable formulas. -/
structure Formula1 where
  code : Nat
deriving DecidableEq

/-- Canonical formula parameter used for the pointed induction witness. -/
def phi0 : Formula1 := { code := 0 }

/-- Explicit base/step components of the recursive Peano axioms and induction. -/
inductive PeanoAxiomComponent
  | add_base
  | add_step
  | mul_base
  | mul_step
  | induction_base (phi : Formula1)
  | induction_step (phi : Formula1)
deriving DecidableEq

/-- Component-level interface: read only the family and formula parameter. -/
inductive PAComponentInterface
  | componentTrace
deriving DecidableEq

/-- Family of a Peano axiom component. -/
inductive ComponentFamily
  | addition
  | multiplication
  | induction
deriving DecidableEq

/-- R1 observation value for axiom components. -/
structure ComponentTrace where
  family : ComponentFamily
  formulaCode : Nat
deriving DecidableEq

/-- The active component-level R1 interface reads family and formula parameter. -/
def I_PA_component : Subfamily PAComponentInterface
  | PAComponentInterface.componentTrace => True

/-- Observation map for explicit Peano axiom components. -/
def obs_PA_component : PAComponentInterface → PeanoAxiomComponent → ComponentTrace
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.add_base =>
      { family := ComponentFamily.addition, formulaCode := 0 }
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.add_step =>
      { family := ComponentFamily.addition, formulaCode := 0 }
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.mul_base =>
      { family := ComponentFamily.multiplication, formulaCode := 0 }
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.mul_step =>
      { family := ComponentFamily.multiplication, formulaCode := 0 }
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.induction_base phi =>
      { family := ComponentFamily.induction, formulaCode := phi.code }
  | PAComponentInterface.componentTrace, PeanoAxiomComponent.induction_step phi =>
      { family := ComponentFamily.induction, formulaCode := phi.code }

/-- Target map for explicit Peano axiom components: read base/step. -/
def sigma_PA_component : PeanoAxiomComponent → Phase
  | PeanoAxiomComponent.add_base => Phase.base
  | PeanoAxiomComponent.add_step => Phase.step
  | PeanoAxiomComponent.mul_base => Phase.base
  | PeanoAxiomComponent.mul_step => Phase.step
  | PeanoAxiomComponent.induction_base _phi => Phase.base
  | PeanoAxiomComponent.induction_step _phi => Phase.step

/-- Component-level finite base/step mediator. -/
def M_PA_component : PeanoAxiomComponent → Fin 2 :=
  fun a => phaseToFin (sigma_PA_component a)

/-- Canonical induction base component. -/
def x_induction_base : PeanoAxiomComponent :=
  PeanoAxiomComponent.induction_base phi0

/-- Canonical induction step component. -/
def y_induction_step : PeanoAxiomComponent :=
  PeanoAxiomComponent.induction_step phi0

/-- The canonical induction component pair. -/
def canonicalPair_PA_component :
    PeanoAxiomComponent × PeanoAxiomComponent :=
  (x_induction_base, y_induction_step)

/-- The target separates the canonical induction component pair. -/
theorem requiredAtCanonicalPair_PA_component :
    RequiredDistinction sigma_PA_component
      canonicalPair_PA_component.1 canonicalPair_PA_component.2 := by
  exact Phase.base_ne_step

/--
The active R1 interface sees the same induction family and formula parameter on
the canonical component pair.
-/
theorem jointSameAtCanonicalPair_PA_component :
    JointSame obs_PA_component I_PA_component
      canonicalPair_PA_component.1 canonicalPair_PA_component.2 := by
  intro j _hj
  cases j
  rfl

/-- The canonical induction component pair is a diagonalization witness. -/
theorem canonicalDiagonalWitness_PA_component :
    DiagonalizationWitness obs_PA_component sigma_PA_component I_PA_component
      canonicalPair_PA_component.1 canonicalPair_PA_component.2 :=
  ⟨requiredAtCanonicalPair_PA_component,
    jointSameAtCanonicalPair_PA_component⟩

/-- The component-level residual is nonempty. -/
theorem residualNonempty_PA_component :
    ResidualNonempty_R2 obs_PA_component sigma_PA_component I_PA_component :=
  ⟨canonicalPair_PA_component.1,
    canonicalPair_PA_component.2,
    canonicalDiagonalWitness_PA_component⟩

/-- The component mediator separates every component-level diagonal witness. -/
theorem M_PA_component_separates_witnesses :
    ∀ x y : PeanoAxiomComponent,
      DiagonalizationWitness obs_PA_component sigma_PA_component
        I_PA_component x y →
        M_PA_component x ≠ M_PA_component y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_component x = sigma_PA_component y :=
    phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The component mediator closes the mediated residual. -/
theorem mediatedResidualEmpty_M_PA_component :
    MediatedResidualEmpty obs_PA_component sigma_PA_component
      I_PA_component M_PA_component := by
  intro x y hResidual
  exact
    (M_PA_component_separates_witnesses x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The component mediator separates the canonical induction component pair. -/
theorem M_PA_component_separates_canonicalPair :
    M_PA_component canonicalPair_PA_component.1 ≠
      M_PA_component canonicalPair_PA_component.2 :=
  phaseToFin_base_ne_step

/-- Any proper active component subfamily omits the single trace reader. -/
theorem not_mem_of_proper_component_subfamily
    (K : Subfamily PAComponentInterface) :
    Subfamily.Proper K I_PA_component →
      ¬ K PAComponentInterface.componentTrace := by
  intro hProper
  rcases hProper.2 with ⟨j, _hIj, hNotK⟩
  cases j
  exact hNotK

/-- The canonical component pair is indistinguishable for every proper subfamily. -/
theorem jointSameAtCanonicalPair_component_of_properSubfamily
    (K : Subfamily PAComponentInterface)
    (hProper : Subfamily.Proper K I_PA_component) :
    JointSame obs_PA_component K
      canonicalPair_PA_component.1 canonicalPair_PA_component.2 := by
  intro j hj
  cases j
  exact False.elim ((not_mem_of_proper_component_subfamily K hProper) hj)

/-- Explicit component-level non-descent witness for every proper subfamily. -/
theorem witnessedIrreducibleMediator_M_PA_component :
    WitnessedIrreducibleMediator
      obs_PA_component I_PA_component M_PA_component := by
  intro K hProper
  exact
    ⟨canonicalPair_PA_component.1,
      canonicalPair_PA_component.2,
      jointSameAtCanonicalPair_component_of_properSubfamily K hProper,
      M_PA_component_separates_canonicalPair⟩

/-- The component mediator does not descend to any proper active subfamily. -/
theorem irreducibleMediator_M_PA_component :
    IrreducibleMediator obs_PA_component I_PA_component M_PA_component :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_component I_PA_component M_PA_component
    witnessedIrreducibleMediator_M_PA_component

/-- The component mediator gives a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_PA_component :
    ProperMediatedR2Certificate
      obs_PA_component sigma_PA_component I_PA_component M_PA_component :=
  ⟨residualNonempty_PA_component,
    mediatedResidualEmpty_M_PA_component,
    irreducibleMediator_M_PA_component⟩

/-- The component mediator gives a witnessed proper mediated R2 certificate. -/
theorem witnessedProperMediatedR2Certificate_M_PA_component :
    WitnessedProperMediatedR2Certificate
      obs_PA_component sigma_PA_component I_PA_component M_PA_component :=
  ⟨residualNonempty_PA_component,
    mediatedResidualEmpty_M_PA_component,
    witnessedIrreducibleMediator_M_PA_component⟩

/-- No smaller component-level proper mediated certificate exists below `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_component :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_component sigma_PA_component I_PA_component m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_component sigma_PA_component I_PA_component
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_component sigma_PA_component I_PA_component
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- The component mediator realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_component :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_component sigma_PA_component I_PA_component M_PA_component :=
  ⟨properMediatedR2Certificate_M_PA_component,
    no_smaller_properMediatedR2Certificate_PA_component⟩

/-- The component mediator realizes dimension-minimal witnessed proper closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_component :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      obs_PA_component sigma_PA_component I_PA_component M_PA_component :=
  ⟨witnessedProperMediatedR2Certificate_M_PA_component,
    no_smaller_properMediatedR2Certificate_PA_component⟩

/-- The exact proper mediated R2 dimension of the component certificate is `2`. -/
theorem exactProperMediatedR2Dimension_two_PA_component :
    ExactProperMediatedR2Dimension
      obs_PA_component sigma_PA_component I_PA_component 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_component

/-- End-to-end extraction of the Peano component-level certificate package. -/
theorem endToEnd_PA_component :
    ResidualNonempty_R2 obs_PA_component sigma_PA_component I_PA_component
      ∧ MediatedResidualEmpty
          obs_PA_component sigma_PA_component I_PA_component M_PA_component
      ∧ IrreducibleMediator obs_PA_component I_PA_component M_PA_component
      ∧ (∀ m : Nat,
          m < 2 →
            ¬ ExistsProperMediatedR2CertificateAtDim
              obs_PA_component sigma_PA_component I_PA_component m) :=
  endToEnd_staticProperMediatedR2Certificate
    obs_PA_component sigma_PA_component I_PA_component M_PA_component
    dimensionMinimalProperMediatedR2Certificate_M_PA_component

/-
Dynamic lift.

The dynamic layer indexes the same axiom-level certificate by a step type.  The
target can vary with a step in the general framework; here the Peano axiom-level
readout is stable across steps, giving a uniform proper mediated R2 certificate.
-/

/-- Dynamic step type for the recursive Peano axiom fragment. -/
inductive PARecDynamicStep
  | recursion
deriving DecidableEq

/-- Dynamic target for the recursive axiom fragment. -/
def target_PA_axiom_dynamic :
    DynamicTarget PARecAxiom PARecDynamicStep Phase :=
  { targetAt := fun _step => sigma_PA_axiom }

/-- Step-indexed mediator for the recursive axiom fragment. -/
def M_PA_axiom_dynamic :
    PARecDynamicStep → PARecAxiom → Fin 2 :=
  fun _step => M_PA_axiom

/-- The canonical recursive pair is a dynamic diagonal witness at every step. -/
theorem dynamicCanonicalDiagonalWitness_PA_axiom
    (step : PARecDynamicStep) :
    DynamicDiagonalizationWitness
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step
      canonicalPair_PA_axiom.1 canonicalPair_PA_axiom.2 := by
  cases step
  exact canonicalDiagonalWitness_PA_axiom

/-- The recursive dynamic residual is nonempty at every step. -/
theorem dynamicResidualNonempty_PA_axiom
    (step : PARecDynamicStep) :
    DynamicResidualNonempty_R2
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step := by
  cases step
  exact residualNonempty_PA_axiom

/-- The recursive mediator closes the dynamic mediated residual at every step. -/
theorem dynamicMediatedResidualEmpty_M_PA_axiom
    (step : PARecDynamicStep) :
    DynamicMediatedResidualEmpty
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step
      (M_PA_axiom_dynamic step) := by
  cases step
  exact mediatedResidualEmpty_M_PA_axiom

/-- Uniform dynamic certificate for the recursive Peano axiom fragment. -/
theorem uniformProperMediatedR2Certificate_M_PA_axiom_dynamic :
    UniformProperMediatedR2Certificate
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom
      M_PA_axiom_dynamic :=
  ⟨fun _step => residualNonempty_PA_axiom,
    fun _step => mediatedResidualEmpty_M_PA_axiom,
    fun _step => irreducibleMediator_M_PA_axiom⟩

/-- Every recursive dynamic step gives the corresponding stepwise certificate. -/
theorem stepwiseProperMediatedR2Certificate_M_PA_axiom_dynamic
    (step : PARecDynamicStep) :
    StepwiseProperMediatedR2Certificate
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step
      (M_PA_axiom_dynamic step) :=
  stepwiseProperMediatedR2Certificate_of_uniform
    uniformProperMediatedR2Certificate_M_PA_axiom_dynamic step

/-- Every recursive dynamic step gives the witnessed stepwise certificate. -/
theorem stepwiseWitnessedProperMediatedR2Certificate_M_PA_axiom_dynamic
    (step : PARecDynamicStep) :
    StepwiseWitnessedProperMediatedR2Certificate
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step
      (M_PA_axiom_dynamic step) := by
  cases step
  exact witnessedProperMediatedR2Certificate_M_PA_axiom

/-- Every recursive dynamic step has exact proper mediated R2 dimension `2`. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_axiom
    (step : PARecDynamicStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step 2 := by
  cases step
  exact exactProperMediatedR2Dimension_two_PA_axiom

/-- The uniform recursive dynamic certificate rules out direct dynamic closure. -/
theorem not_dynamicClosed_R2_PA_axiom
    (step : PARecDynamicStep) :
    ¬ DynamicClosed_R2 obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_axiom target_PA_axiom_dynamic I_PA_axiom M_PA_axiom_dynamic
    uniformProperMediatedR2Certificate_M_PA_axiom_dynamic step

/-- Dynamic step type for explicit Peano axiom components. -/
inductive PAComponentDynamicStep
  | component
deriving DecidableEq

/-- Dynamic target for explicit Peano axiom components. -/
def target_PA_component_dynamic :
    DynamicTarget PeanoAxiomComponent PAComponentDynamicStep Phase :=
  { targetAt := fun _step => sigma_PA_component }

/-- Step-indexed mediator for explicit Peano axiom components. -/
def M_PA_component_dynamic :
    PAComponentDynamicStep → PeanoAxiomComponent → Fin 2 :=
  fun _step => M_PA_component

/-- The canonical component pair is a dynamic diagonal witness at every step. -/
theorem dynamicCanonicalDiagonalWitness_PA_component
    (step : PAComponentDynamicStep) :
    DynamicDiagonalizationWitness
      obs_PA_component target_PA_component_dynamic I_PA_component step
      canonicalPair_PA_component.1 canonicalPair_PA_component.2 := by
  cases step
  exact canonicalDiagonalWitness_PA_component

/-- The component dynamic residual is nonempty at every step. -/
theorem dynamicResidualNonempty_PA_component
    (step : PAComponentDynamicStep) :
    DynamicResidualNonempty_R2
      obs_PA_component target_PA_component_dynamic I_PA_component step := by
  cases step
  exact residualNonempty_PA_component

/-- The component mediator closes the dynamic mediated residual at every step. -/
theorem dynamicMediatedResidualEmpty_M_PA_component
    (step : PAComponentDynamicStep) :
    DynamicMediatedResidualEmpty
      obs_PA_component target_PA_component_dynamic I_PA_component step
      (M_PA_component_dynamic step) := by
  cases step
  exact mediatedResidualEmpty_M_PA_component

/-- Uniform dynamic certificate for explicit Peano axiom components. -/
theorem uniformProperMediatedR2Certificate_M_PA_component_dynamic :
    UniformProperMediatedR2Certificate
      obs_PA_component target_PA_component_dynamic I_PA_component
      M_PA_component_dynamic :=
  ⟨fun _step => residualNonempty_PA_component,
    fun _step => mediatedResidualEmpty_M_PA_component,
    fun _step => irreducibleMediator_M_PA_component⟩

/-- Every component dynamic step gives the corresponding stepwise certificate. -/
theorem stepwiseProperMediatedR2Certificate_M_PA_component_dynamic
    (step : PAComponentDynamicStep) :
    StepwiseProperMediatedR2Certificate
      obs_PA_component target_PA_component_dynamic I_PA_component step
      (M_PA_component_dynamic step) :=
  stepwiseProperMediatedR2Certificate_of_uniform
    uniformProperMediatedR2Certificate_M_PA_component_dynamic step

/-- Every component dynamic step gives the witnessed stepwise certificate. -/
theorem stepwiseWitnessedProperMediatedR2Certificate_M_PA_component_dynamic
    (step : PAComponentDynamicStep) :
    StepwiseWitnessedProperMediatedR2Certificate
      obs_PA_component target_PA_component_dynamic I_PA_component step
      (M_PA_component_dynamic step) := by
  cases step
  exact witnessedProperMediatedR2Certificate_M_PA_component

/-- Every component dynamic step has exact proper mediated R2 dimension `2`. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_component
    (step : PAComponentDynamicStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_component target_PA_component_dynamic I_PA_component step 2 := by
  cases step
  exact exactProperMediatedR2Dimension_two_PA_component

/-- The uniform component dynamic certificate rules out direct dynamic closure. -/
theorem not_dynamicClosed_R2_PA_component
    (step : PAComponentDynamicStep) :
    ¬ DynamicClosed_R2
      obs_PA_component target_PA_component_dynamic I_PA_component step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_component target_PA_component_dynamic I_PA_component
    M_PA_component_dynamic
    uniformProperMediatedR2Certificate_M_PA_component_dynamic step

/-
Nontrivial component dynamics.

Here the dynamic step selects the active Peano axiom pair.  Unlike the uniform
stable lift above, the target genuinely varies with the step.
-/

/-- A dynamic step selecting the currently active Peano axiom component pair. -/
inductive PAComponentActiveStep
  | addition
  | multiplication
  | induction (formulaCode : Nat)
deriving DecidableEq

/-- Base/step target for the addition component pair. -/
def sigma_PA_component_addition : PeanoAxiomComponent → Phase
  | PeanoAxiomComponent.add_base => Phase.base
  | PeanoAxiomComponent.add_step => Phase.step
  | PeanoAxiomComponent.mul_base => Phase.base
  | PeanoAxiomComponent.mul_step => Phase.base
  | PeanoAxiomComponent.induction_base _phi => Phase.base
  | PeanoAxiomComponent.induction_step _phi => Phase.base

/-- Base/step target for the multiplication component pair. -/
def sigma_PA_component_multiplication : PeanoAxiomComponent → Phase
  | PeanoAxiomComponent.add_base => Phase.base
  | PeanoAxiomComponent.add_step => Phase.base
  | PeanoAxiomComponent.mul_base => Phase.base
  | PeanoAxiomComponent.mul_step => Phase.step
  | PeanoAxiomComponent.induction_base _phi => Phase.base
  | PeanoAxiomComponent.induction_step _phi => Phase.base

/-- Base/step target for induction components. -/
def sigma_PA_component_induction : PeanoAxiomComponent → Phase
  | PeanoAxiomComponent.add_base => Phase.base
  | PeanoAxiomComponent.add_step => Phase.base
  | PeanoAxiomComponent.mul_base => Phase.base
  | PeanoAxiomComponent.mul_step => Phase.base
  | PeanoAxiomComponent.induction_base _phi => Phase.base
  | PeanoAxiomComponent.induction_step _phi => Phase.step

/-- Step-dependent base/step target for explicit Peano axiom components. -/
def sigma_PA_component_at : PAComponentActiveStep → PeanoAxiomComponent → Phase
  | PAComponentActiveStep.addition => sigma_PA_component_addition
  | PAComponentActiveStep.multiplication => sigma_PA_component_multiplication
  | PAComponentActiveStep.induction _formulaCode => sigma_PA_component_induction

/-- Nontrivial dynamic target: the active base/step pair depends on the step. -/
def target_PA_component_active :
    DynamicTarget PeanoAxiomComponent PAComponentActiveStep Phase :=
  { targetAt := sigma_PA_component_at }

/-- Step-dependent mediator for the active Peano axiom component pair. -/
def M_PA_component_active :
    PAComponentActiveStep → PeanoAxiomComponent → Fin 2 :=
  fun step x => phaseToFin (sigma_PA_component_at step x)

/-- Canonical active component pair for each dynamic step. -/
def activePair_PA_component :
    PAComponentActiveStep → PeanoAxiomComponent × PeanoAxiomComponent
  | PAComponentActiveStep.addition =>
      (PeanoAxiomComponent.add_base, PeanoAxiomComponent.add_step)
  | PAComponentActiveStep.multiplication =>
      (PeanoAxiomComponent.mul_base, PeanoAxiomComponent.mul_step)
  | PAComponentActiveStep.induction formulaCode =>
      (PeanoAxiomComponent.induction_base { code := formulaCode },
        PeanoAxiomComponent.induction_step { code := formulaCode })

/-- The active dynamic target separates the active pair at each step. -/
theorem requiredAtActivePair_PA_component
    (step : PAComponentActiveStep) :
    RequiredDistinction (target_PA_component_active.targetAt step)
      (activePair_PA_component step).1 (activePair_PA_component step).2 := by
  cases step with
  | addition =>
      exact Phase.base_ne_step
  | multiplication =>
      exact Phase.base_ne_step
  | induction formulaCode =>
      exact Phase.base_ne_step

/-- The active pair remains indistinguishable by the component R1 interface. -/
theorem jointSameAtActivePair_PA_component
    (step : PAComponentActiveStep) :
    JointSame obs_PA_component I_PA_component
      (activePair_PA_component step).1 (activePair_PA_component step).2 := by
  intro j _hj
  cases j
  cases step with
  | addition =>
      rfl
  | multiplication =>
      rfl
  | induction formulaCode =>
      rfl

/-- The active pair is a dynamic diagonal witness at each nontrivial step. -/
theorem dynamicCanonicalDiagonalWitness_PA_component_active
    (step : PAComponentActiveStep) :
    DynamicDiagonalizationWitness
      obs_PA_component target_PA_component_active I_PA_component step
      (activePair_PA_component step).1 (activePair_PA_component step).2 :=
  ⟨requiredAtActivePair_PA_component step,
    jointSameAtActivePair_PA_component step⟩

/-- The nontrivial component dynamic residual is nonempty at every step. -/
theorem dynamicResidualNonempty_PA_component_active
    (step : PAComponentActiveStep) :
    DynamicResidualNonempty_R2
      obs_PA_component target_PA_component_active I_PA_component step :=
  ⟨(activePair_PA_component step).1,
    (activePair_PA_component step).2,
    dynamicCanonicalDiagonalWitness_PA_component_active step⟩

/-- The active mediator separates every dynamic diagonal witness at each step. -/
theorem M_PA_component_active_separates_witnesses
    (step : PAComponentActiveStep) :
    ∀ x y : PeanoAxiomComponent,
      DynamicDiagonalizationWitness
        obs_PA_component target_PA_component_active I_PA_component step x y →
        M_PA_component_active step x ≠ M_PA_component_active step y := by
  intro x y hWitness hM
  have hPhase :
      target_PA_component_active.targetAt step x =
        target_PA_component_active.targetAt step y :=
    phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The active mediator closes the nontrivial dynamic mediated residual. -/
theorem dynamicMediatedResidualEmpty_M_PA_component_active
    (step : PAComponentActiveStep) :
    DynamicMediatedResidualEmpty
      obs_PA_component target_PA_component_active I_PA_component step
      (M_PA_component_active step) := by
  intro x y hResidual
  exact
    (M_PA_component_active_separates_witnesses step x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The active mediator separates the active pair at each step. -/
theorem M_PA_component_active_separates_pair
    (step : PAComponentActiveStep) :
    M_PA_component_active step (activePair_PA_component step).1 ≠
      M_PA_component_active step (activePair_PA_component step).2 := by
  exact
    M_PA_component_active_separates_witnesses step
      (activePair_PA_component step).1
      (activePair_PA_component step).2
      (dynamicCanonicalDiagonalWitness_PA_component_active step)

/-- The active pair is indistinguishable for every proper component subfamily. -/
theorem jointSameAtActivePair_component_of_properSubfamily
    (step : PAComponentActiveStep)
    (K : Subfamily PAComponentInterface)
    (hProper : Subfamily.Proper K I_PA_component) :
    JointSame obs_PA_component K
      (activePair_PA_component step).1 (activePair_PA_component step).2 := by
  intro j hj
  cases j
  exact False.elim ((not_mem_of_proper_component_subfamily K hProper) hj)

/-- Explicit non-descent witnesses for the active mediator at every step. -/
theorem witnessedIrreducibleMediator_M_PA_component_active
    (step : PAComponentActiveStep) :
    WitnessedIrreducibleMediator
      obs_PA_component I_PA_component (M_PA_component_active step) := by
  intro K hProper
  exact
    ⟨(activePair_PA_component step).1,
      (activePair_PA_component step).2,
      jointSameAtActivePair_component_of_properSubfamily step K hProper,
      M_PA_component_active_separates_pair step⟩

/-- The active mediator is irreducible at every nontrivial dynamic step. -/
theorem irreducibleMediator_M_PA_component_active
    (step : PAComponentActiveStep) :
    IrreducibleMediator
      obs_PA_component I_PA_component (M_PA_component_active step) :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_component I_PA_component (M_PA_component_active step)
    (witnessedIrreducibleMediator_M_PA_component_active step)

/-- Uniform proper mediated R2 certificate for the nontrivial component dynamics. -/
theorem uniformProperMediatedR2Certificate_M_PA_component_active :
    UniformProperMediatedR2Certificate
      obs_PA_component target_PA_component_active I_PA_component
      M_PA_component_active :=
  ⟨dynamicResidualNonempty_PA_component_active,
    dynamicMediatedResidualEmpty_M_PA_component_active,
    irreducibleMediator_M_PA_component_active⟩

/-- Stepwise proper certificate for the nontrivial component dynamics. -/
theorem stepwiseProperMediatedR2Certificate_M_PA_component_active
    (step : PAComponentActiveStep) :
    StepwiseProperMediatedR2Certificate
      obs_PA_component target_PA_component_active I_PA_component step
      (M_PA_component_active step) :=
  stepwiseProperMediatedR2Certificate_of_uniform
    uniformProperMediatedR2Certificate_M_PA_component_active step

/-- Stepwise witnessed certificate for the nontrivial component dynamics. -/
theorem stepwiseWitnessedProperMediatedR2Certificate_M_PA_component_active
    (step : PAComponentActiveStep) :
    StepwiseWitnessedProperMediatedR2Certificate
      obs_PA_component target_PA_component_active I_PA_component step
      (M_PA_component_active step) :=
  ⟨dynamicResidualNonempty_PA_component_active step,
    dynamicMediatedResidualEmpty_M_PA_component_active step,
    witnessedIrreducibleMediator_M_PA_component_active step⟩

/-- Each active dynamic component step has exact proper mediated dimension `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_component_active
    (step : PAComponentActiveStep) :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_component (target_PA_component_active.targetAt step)
          I_PA_component m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        obs_PA_component (target_PA_component_active.targetAt step)
        I_PA_component
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            obs_PA_component (target_PA_component_active.targetAt step)
            I_PA_component
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- Each active dynamic component step has exact proper mediated dimension `2`. -/
theorem dynamicExactProperMediatedR2Dimension_two_PA_component_active
    (step : PAComponentActiveStep) :
    DynamicExactProperMediatedR2Dimension
      obs_PA_component target_PA_component_active I_PA_component step 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    ⟨stepwiseProperMediatedR2Certificate_M_PA_component_active step,
      no_smaller_properMediatedR2Certificate_PA_component_active step⟩

/-- Nontrivial active component dynamics rules out direct dynamic closure. -/
theorem not_dynamicClosed_R2_PA_component_active
    (step : PAComponentActiveStep) :
    ¬ DynamicClosed_R2
      obs_PA_component target_PA_component_active I_PA_component step :=
  uniformProperMediatedR2Certificate_not_closed_at_step
    obs_PA_component target_PA_component_active I_PA_component
    M_PA_component_active
    uniformProperMediatedR2Certificate_M_PA_component_active step

end PeanoAxiomLevelDynamic
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PARecAxiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PARecInterface
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.RecFamily
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.Phase
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.I_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.obs_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.phaseToFin
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.canonicalDiagonalWitness_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.residualNonempty_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_axiom_separates_witnesses
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.mediatedResidualEmpty_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.witnessedIrreducibleMediator_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.irreducibleMediator_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.properMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.witnessedProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dimensionMinimalProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.exactProperMediatedR2Dimension_two_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.endToEnd_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.Formula1
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PeanoAxiomComponent
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PAComponentInterface
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.ComponentFamily
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.ComponentTrace
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.I_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.obs_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.canonicalDiagonalWitness_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.residualNonempty_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_component_separates_witnesses
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.mediatedResidualEmpty_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.witnessedIrreducibleMediator_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.irreducibleMediator_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.properMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.witnessedProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dimensionMinimalProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.exactProperMediatedR2Dimension_two_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.endToEnd_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PARecDynamicStep
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.target_PA_axiom_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_axiom_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicCanonicalDiagonalWitness_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicResidualNonempty_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicMediatedResidualEmpty_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.uniformProperMediatedR2Certificate_M_PA_axiom_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseProperMediatedR2Certificate_M_PA_axiom_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseWitnessedProperMediatedR2Certificate_M_PA_axiom_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicExactProperMediatedR2Dimension_two_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.not_dynamicClosed_R2_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PAComponentDynamicStep
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.target_PA_component_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_component_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicCanonicalDiagonalWitness_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicResidualNonempty_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicMediatedResidualEmpty_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.uniformProperMediatedR2Certificate_M_PA_component_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseProperMediatedR2Certificate_M_PA_component_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseWitnessedProperMediatedR2Certificate_M_PA_component_dynamic
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicExactProperMediatedR2Dimension_two_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.not_dynamicClosed_R2_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.PAComponentActiveStep
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_component_addition
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_component_multiplication
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_component_induction
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.sigma_PA_component_at
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.target_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.activePair_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicCanonicalDiagonalWitness_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicResidualNonempty_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.M_PA_component_active_separates_witnesses
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicMediatedResidualEmpty_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.witnessedIrreducibleMediator_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.irreducibleMediator_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.uniformProperMediatedR2Certificate_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseProperMediatedR2Certificate_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.stepwiseWitnessedProperMediatedR2Certificate_M_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.no_smaller_properMediatedR2Certificate_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.dynamicExactProperMediatedR2Dimension_two_PA_component_active
#print axioms LocalSemanticClosure.PeanoAxiomLevelDynamic.not_dynamicClosed_R2_PA_component_active
/- AXIOM_AUDIT_END -/
