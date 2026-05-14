import RegimesSelfContained

/-!
# Peano axiom-level R1/R2 certificate

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
namespace PeanoAxiomLevel

open Standalone.RegimesSelfContained

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

end PeanoAxiomLevel
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.PeanoAxiomLevel.PARecAxiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.PARecInterface
#print axioms LocalSemanticClosure.PeanoAxiomLevel.RecFamily
#print axioms LocalSemanticClosure.PeanoAxiomLevel.Phase
#print axioms LocalSemanticClosure.PeanoAxiomLevel.I_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.obs_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.sigma_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.phaseToFin
#print axioms LocalSemanticClosure.PeanoAxiomLevel.M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.canonicalDiagonalWitness_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.residualNonempty_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.M_PA_axiom_separates_witnesses
#print axioms LocalSemanticClosure.PeanoAxiomLevel.mediatedResidualEmpty_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.witnessedIrreducibleMediator_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.irreducibleMediator_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.properMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.witnessedProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.dimensionMinimalProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.exactProperMediatedR2Dimension_two_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.endToEnd_PA_axiom
#print axioms LocalSemanticClosure.PeanoAxiomLevel.Formula1
#print axioms LocalSemanticClosure.PeanoAxiomLevel.PeanoAxiomComponent
#print axioms LocalSemanticClosure.PeanoAxiomLevel.PAComponentInterface
#print axioms LocalSemanticClosure.PeanoAxiomLevel.ComponentFamily
#print axioms LocalSemanticClosure.PeanoAxiomLevel.ComponentTrace
#print axioms LocalSemanticClosure.PeanoAxiomLevel.I_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.obs_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.sigma_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.canonicalDiagonalWitness_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.residualNonempty_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.M_PA_component_separates_witnesses
#print axioms LocalSemanticClosure.PeanoAxiomLevel.mediatedResidualEmpty_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.witnessedIrreducibleMediator_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.irreducibleMediator_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.properMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.witnessedProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.dimensionMinimalProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.exactProperMediatedR2Dimension_two_PA_component
#print axioms LocalSemanticClosure.PeanoAxiomLevel.endToEnd_PA_component
/- AXIOM_AUDIT_END -/
