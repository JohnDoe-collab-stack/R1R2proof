import RegimesSelfContained

/-!
# Peano PA formula axioms and R1/R2 certificates

This file is a fresh, formula-level Peano instance.

The objects are not Lean axioms and they are not informal labels.  They are
first-order syntax trees:

* terms with variables, zero, successor, addition, and multiplication;
* formulas with equality, negation, implication, conjunction, and universal
  quantification;
* the usual first-order Peano axiom formulas for successor, addition,
  multiplication, and the induction schema.

The R1/R2 certificate is then instantiated on these formula objects.

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace PeanoPAFormulaAxioms

open Standalone.RegimesSelfContained

/-- First-order terms for the language of Peano arithmetic. -/
inductive Term
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
deriving DecidableEq

/-- First-order formulas for the language of Peano arithmetic. -/
inductive Formula
  | falsum : Formula
  | equal : Term → Term → Formula
  | not : Formula → Formula
  | imp : Formula → Formula → Formula
  | and : Formula → Formula → Formula
  | forallE : Nat → Formula → Formula
deriving DecidableEq

namespace Term

/-- Substitute a term for one named variable in a term. -/
def subst (target : Nat) (replacement : Term) : Term → Term
  | var n =>
      match Nat.decEq n target with
      | isTrue _ => replacement
      | isFalse _ => var n
  | zero => zero
  | succ t => succ (subst target replacement t)
  | add lhs rhs => add (subst target replacement lhs) (subst target replacement rhs)
  | mul lhs rhs => mul (subst target replacement lhs) (subst target replacement rhs)

end Term

namespace Formula

/--
Substitute a term for one named free variable in a formula.

If the same variable is bound by a universal quantifier, substitution stops
under that binder.
-/
def subst (target : Nat) (replacement : Term) : Formula → Formula
  | falsum => falsum
  | equal lhs rhs =>
      equal (Term.subst target replacement lhs)
        (Term.subst target replacement rhs)
  | not p => not (subst target replacement p)
  | imp p q => imp (subst target replacement p) (subst target replacement q)
  | and p q => and (subst target replacement p) (subst target replacement q)
  | forallE n p =>
      match Nat.decEq n target with
      | isTrue _ => forallE n p
      | isFalse _ => forallE n (subst target replacement p)

/-- Syntactic inequality. -/
def notEqual (lhs rhs : Term) : Formula :=
  not (equal lhs rhs)

end Formula

/-- Variable `x`. -/
def xTerm : Term := Term.var 0

/-- Variable `y`. -/
def yTerm : Term := Term.var 1

/-- `∀ x, S x ≠ 0`. -/
def paSuccNeZeroFormula : Formula :=
  Formula.forallE 0
    (Formula.notEqual (Term.succ xTerm) Term.zero)

/-- `∀ x y, S x = S y → x = y`. -/
def paSuccInjectiveFormula : Formula :=
  Formula.forallE 0
    (Formula.forallE 1
      (Formula.imp
        (Formula.equal (Term.succ xTerm) (Term.succ yTerm))
        (Formula.equal xTerm yTerm)))

/-- `∀ x, x + 0 = x`. -/
def paAddZeroFormula : Formula :=
  Formula.forallE 0
    (Formula.equal (Term.add xTerm Term.zero) xTerm)

/-- `∀ x y, x + S y = S (x + y)`. -/
def paAddSuccFormula : Formula :=
  Formula.forallE 0
    (Formula.forallE 1
      (Formula.equal
        (Term.add xTerm (Term.succ yTerm))
        (Term.succ (Term.add xTerm yTerm))))

/-- `∀ x, x * 0 = 0`. -/
def paMulZeroFormula : Formula :=
  Formula.forallE 0
    (Formula.equal (Term.mul xTerm Term.zero) Term.zero)

/-- `∀ x y, x * S y = (x * y) + x`. -/
def paMulSuccFormula : Formula :=
  Formula.forallE 0
    (Formula.forallE 1
      (Formula.equal
        (Term.mul xTerm (Term.succ yTerm))
        (Term.add (Term.mul xTerm yTerm) xTerm)))

/-- The base instance `phi(0)` of a one-variable formula `phi(x)`. -/
def inductionBaseFormula (phi : Formula) : Formula :=
  Formula.subst 0 Term.zero phi

/-- The step premise `∀ x, phi(x) → phi(S x)`. -/
def inductionStepFormula (phi : Formula) : Formula :=
  Formula.forallE 0
    (Formula.imp phi
      (Formula.subst 0 (Term.succ xTerm) phi))

/-- The conclusion `∀ x, phi(x)`. -/
def inductionConclusionFormula (phi : Formula) : Formula :=
  Formula.forallE 0 phi

/-- The induction axiom `(phi(0) ∧ ∀ x, phi(x) → phi(S x)) → ∀ x, phi(x)`. -/
def paInductionFormula (phi : Formula) : Formula :=
  Formula.imp
    (Formula.and
      (inductionBaseFormula phi)
      (inductionStepFormula phi))
    (inductionConclusionFormula phi)

/-- Canonical one-variable formula parameter used for pointed witnesses. -/
def phi0 : Formula :=
  Formula.equal xTerm xTerm

/--
Witness that a formula is one of the first-order Peano axiom formulas.

This is a type-valued certificate attached to the formula itself.  The object
being carried is the formula, not just an informal axiom name.
-/
inductive IsPAFormulaAxiom : Formula → Type
  | succ_ne_zero : IsPAFormulaAxiom paSuccNeZeroFormula
  | succ_injective : IsPAFormulaAxiom paSuccInjectiveFormula
  | add_zero : IsPAFormulaAxiom paAddZeroFormula
  | add_succ : IsPAFormulaAxiom paAddSuccFormula
  | mul_zero : IsPAFormulaAxiom paMulZeroFormula
  | mul_succ : IsPAFormulaAxiom paMulSuccFormula
  | induction (phi : Formula) : IsPAFormulaAxiom (paInductionFormula phi)

/-- A Peano axiom as an actual formula together with its syntactic certificate. -/
structure PAFormulaAxiom where
  formula : Formula
  witness : IsPAFormulaAxiom formula

/-- The closed Peano axiom formula `∀ x, S x ≠ 0`. -/
def paSuccNeZeroAxiom : PAFormulaAxiom :=
  ⟨paSuccNeZeroFormula, IsPAFormulaAxiom.succ_ne_zero⟩

/-- The closed Peano axiom formula `∀ x y, S x = S y → x = y`. -/
def paSuccInjectiveAxiom : PAFormulaAxiom :=
  ⟨paSuccInjectiveFormula, IsPAFormulaAxiom.succ_injective⟩

/-- The closed Peano axiom formula `∀ x, x + 0 = x`. -/
def paAddZeroAxiom : PAFormulaAxiom :=
  ⟨paAddZeroFormula, IsPAFormulaAxiom.add_zero⟩

/-- The closed Peano axiom formula `∀ x y, x + S y = S (x + y)`. -/
def paAddSuccAxiom : PAFormulaAxiom :=
  ⟨paAddSuccFormula, IsPAFormulaAxiom.add_succ⟩

/-- The closed Peano axiom formula `∀ x, x * 0 = 0`. -/
def paMulZeroAxiom : PAFormulaAxiom :=
  ⟨paMulZeroFormula, IsPAFormulaAxiom.mul_zero⟩

/-- The closed Peano axiom formula `∀ x y, x * S y = (x * y) + x`. -/
def paMulSuccAxiom : PAFormulaAxiom :=
  ⟨paMulSuccFormula, IsPAFormulaAxiom.mul_succ⟩

/-- The Peano induction axiom formula for an arbitrary one-variable formula. -/
def paInductionAxiom (phi : Formula) : PAFormulaAxiom :=
  ⟨paInductionFormula phi, IsPAFormulaAxiom.induction phi⟩

/-- Peano axiom families visible to the R1 marginal interface. -/
inductive PAFormulaFamily
  | successor
  | addition
  | multiplication
  | induction
deriving DecidableEq

/-- Base/step phase used by the R2 target. -/
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

/-- Trace read by the marginal R1 interface. -/
structure PAFormulaTrace where
  family : PAFormulaFamily
  parameter : Formula
deriving DecidableEq

/-- The inactive/default trace parameter. -/
def noParameter : Formula := Formula.falsum

/-- Family trace of a full Peano axiom formula. -/
def traceOfPAFormulaAxiom : PAFormulaAxiom → PAFormulaTrace
  | ⟨_, IsPAFormulaAxiom.succ_ne_zero⟩ =>
      { family := PAFormulaFamily.successor, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.succ_injective⟩ =>
      { family := PAFormulaFamily.successor, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.add_zero⟩ =>
      { family := PAFormulaFamily.addition, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.add_succ⟩ =>
      { family := PAFormulaFamily.addition, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.mul_zero⟩ =>
      { family := PAFormulaFamily.multiplication, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.mul_succ⟩ =>
      { family := PAFormulaFamily.multiplication, parameter := noParameter }
  | ⟨_, IsPAFormulaAxiom.induction phi⟩ =>
      { family := PAFormulaFamily.induction, parameter := phi }

/--
Phase of a full Peano axiom formula.

The recursive base and step axioms receive their literal phase.  The successor
axioms and the full induction axiom are included as Peano axioms but are not
the pointed base/step residual used below, so they are assigned the base side.
-/
def phaseOfPAFormulaAxiom : PAFormulaAxiom → Phase
  | ⟨_, IsPAFormulaAxiom.succ_ne_zero⟩ => Phase.base
  | ⟨_, IsPAFormulaAxiom.succ_injective⟩ => Phase.base
  | ⟨_, IsPAFormulaAxiom.add_zero⟩ => Phase.base
  | ⟨_, IsPAFormulaAxiom.add_succ⟩ => Phase.step
  | ⟨_, IsPAFormulaAxiom.mul_zero⟩ => Phase.base
  | ⟨_, IsPAFormulaAxiom.mul_succ⟩ => Phase.step
  | ⟨_, IsPAFormulaAxiom.induction _phi⟩ => Phase.base

/-- The singleton interface reads the formula trace. -/
inductive PAFormulaInterface
  | formulaTrace
deriving DecidableEq

/-- Active R1 interface family. -/
def I_PA_formula_axiom : Subfamily PAFormulaInterface
  | PAFormulaInterface.formulaTrace => True

/-- Observation map on actual Peano axiom formulas. -/
def obs_PA_formula_axiom :
    PAFormulaInterface → PAFormulaAxiom → PAFormulaTrace
  | PAFormulaInterface.formulaTrace, a => traceOfPAFormulaAxiom a

/-- R2 target map on actual Peano axiom formulas. -/
def sigma_PA_formula_axiom : PAFormulaAxiom → Phase :=
  phaseOfPAFormulaAxiom

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

/-- Formula-level finite mediator. -/
def M_PA_formula_axiom : PAFormulaAxiom → Fin 2 :=
  fun a => phaseToFin (sigma_PA_formula_axiom a)

/-- The actual Peano axiom formula `∀ x, x + 0 = x`. -/
def x_pa_add_zero : PAFormulaAxiom :=
  paAddZeroAxiom

/-- The actual Peano axiom formula `∀ x y, x + S y = S (x + y)`. -/
def y_pa_add_succ : PAFormulaAxiom :=
  paAddSuccAxiom

/-- The canonical addition pair of actual Peano axiom formulas. -/
def canonicalPair_PA_formula_axiom : PAFormulaAxiom × PAFormulaAxiom :=
  (x_pa_add_zero, y_pa_add_succ)

/-- The target separates the two addition axiom formulas. -/
theorem requiredAtCanonicalPair_PA_formula_axiom :
    RequiredDistinction sigma_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  change Phase.base ≠ Phase.step
  exact Phase.base_ne_step

/-- The active R1 interface sees the same addition trace on the canonical pair. -/
theorem jointSameAtCanonicalPair_PA_formula_axiom :
    JointSame obs_PA_formula_axiom I_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 := by
  intro j _hj
  cases j
  rfl

/-- The canonical pair is a residual witness on actual Peano axiom formulas. -/
theorem canonicalDiagonalWitness_PA_formula_axiom :
    DiagonalizationWitness
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      canonicalPair_PA_formula_axiom.1 canonicalPair_PA_formula_axiom.2 :=
  ⟨requiredAtCanonicalPair_PA_formula_axiom,
    jointSameAtCanonicalPair_PA_formula_axiom⟩

/-- The R2 residual is nonempty at the formula-axiom level. -/
theorem residualNonempty_PA_formula_axiom :
    ResidualNonempty_R2
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom :=
  ⟨canonicalPair_PA_formula_axiom.1,
    canonicalPair_PA_formula_axiom.2,
    canonicalDiagonalWitness_PA_formula_axiom⟩

/-- The mediator separates every formula-axiom residual witness. -/
theorem M_PA_formula_axiom_separates_witnesses :
    ∀ x y : PAFormulaAxiom,
      DiagonalizationWitness
        obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom x y →
        M_PA_formula_axiom x ≠ M_PA_formula_axiom y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_formula_axiom x = sigma_PA_formula_axiom y :=
    phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The mediator closes the formula-axiom mediated residual. -/
theorem mediatedResidualEmpty_M_PA_formula_axiom :
    MediatedResidualEmpty
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom := by
  intro x y hResidual
  exact
    (M_PA_formula_axiom_separates_witnesses x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The mediator separates the canonical pair. -/
theorem M_PA_formula_axiom_separates_canonicalPair :
    M_PA_formula_axiom canonicalPair_PA_formula_axiom.1 ≠
      M_PA_formula_axiom canonicalPair_PA_formula_axiom.2 :=
by
  change phaseToFin Phase.base ≠ phaseToFin Phase.step
  exact phaseToFin_base_ne_step

/-- Any proper active subfamily omits the single formula-trace reader. -/
theorem not_mem_of_proper_formula_axiom_subfamily
    (K : Subfamily PAFormulaInterface) :
    Subfamily.Proper K I_PA_formula_axiom →
      ¬ K PAFormulaInterface.formulaTrace := by
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

/-- The mediator does not descend to any proper active subfamily. -/
theorem irreducibleMediator_M_PA_formula_axiom :
    IrreducibleMediator
      obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom
    witnessedIrreducibleMediator_M_PA_formula_axiom

/-- The actual Peano formula axioms give a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_PA_formula_axiom :
    ProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨residualNonempty_PA_formula_axiom,
    mediatedResidualEmpty_M_PA_formula_axiom,
    irreducibleMediator_M_PA_formula_axiom⟩

/-- Witnessed proper mediated R2 certificate for actual Peano formula axioms. -/
theorem witnessedProperMediatedR2Certificate_M_PA_formula_axiom :
    WitnessedProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨residualNonempty_PA_formula_axiom,
    mediatedResidualEmpty_M_PA_formula_axiom,
    witnessedIrreducibleMediator_M_PA_formula_axiom⟩

/-- No smaller proper mediated certificate exists below dimension `2`. -/
theorem no_smaller_properMediatedR2Certificate_PA_formula_axiom :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          obs_PA_formula_axiom sigma_PA_formula_axiom
          I_PA_formula_axiom m := by
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

/-- Dimension-minimal proper R2 closure for actual Peano formula axioms. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_formula_axiom :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨properMediatedR2Certificate_M_PA_formula_axiom,
    no_smaller_properMediatedR2Certificate_PA_formula_axiom⟩

/-- Dimension-minimal witnessed proper R2 closure for actual formula axioms. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_formula_axiom :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      M_PA_formula_axiom :=
  ⟨witnessedProperMediatedR2Certificate_M_PA_formula_axiom,
    no_smaller_properMediatedR2Certificate_PA_formula_axiom⟩

/-- Exact proper mediated R2 dimension for the formula-axiom certificate. -/
theorem exactProperMediatedR2Dimension_two_PA_formula_axiom :
    ExactProperMediatedR2Dimension
      obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_axiom

/-- End-to-end formula-level Peano axiom package. -/
theorem endToEnd_PA_formula_axiom :
    ResidualNonempty_R2
        obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
      ∧ MediatedResidualEmpty
          obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
          M_PA_formula_axiom
      ∧ IrreducibleMediator
          obs_PA_formula_axiom I_PA_formula_axiom M_PA_formula_axiom
      ∧ (∀ m : Nat,
          m < 2 →
            ¬ ExistsProperMediatedR2CertificateAtDim
              obs_PA_formula_axiom sigma_PA_formula_axiom
              I_PA_formula_axiom m) :=
  endToEnd_staticProperMediatedR2Certificate
    obs_PA_formula_axiom sigma_PA_formula_axiom I_PA_formula_axiom
    M_PA_formula_axiom
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_axiom

/-!
## Component layer

The full induction axiom is a single formula.  To expose its internal
base/step structure, the following layer works on formula components.  The
objects still carry actual first-order formulas.
-/

/-- A formula-level component of Peano arithmetic. -/
inductive IsPAFormulaComponent : Formula → Type
  | succ_ne_zero : IsPAFormulaComponent paSuccNeZeroFormula
  | succ_injective : IsPAFormulaComponent paSuccInjectiveFormula
  | add_base : IsPAFormulaComponent paAddZeroFormula
  | add_step : IsPAFormulaComponent paAddSuccFormula
  | mul_base : IsPAFormulaComponent paMulZeroFormula
  | mul_step : IsPAFormulaComponent paMulSuccFormula
  | induction_base (phi : Formula) :
      IsPAFormulaComponent (inductionBaseFormula phi)
  | induction_step (phi : Formula) :
      IsPAFormulaComponent (inductionStepFormula phi)
  | induction_full (phi : Formula) :
      IsPAFormulaComponent (paInductionFormula phi)

/-- A component object whose main field is the actual formula. -/
structure PAFormulaComponent where
  formula : Formula
  witness : IsPAFormulaComponent formula

/-- Component-level R1 trace. -/
def traceOfPAFormulaComponent : PAFormulaComponent → PAFormulaTrace
  | ⟨_, IsPAFormulaComponent.succ_ne_zero⟩ =>
      { family := PAFormulaFamily.successor, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.succ_injective⟩ =>
      { family := PAFormulaFamily.successor, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.add_base⟩ =>
      { family := PAFormulaFamily.addition, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.add_step⟩ =>
      { family := PAFormulaFamily.addition, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.mul_base⟩ =>
      { family := PAFormulaFamily.multiplication, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.mul_step⟩ =>
      { family := PAFormulaFamily.multiplication, parameter := noParameter }
  | ⟨_, IsPAFormulaComponent.induction_base phi⟩ =>
      { family := PAFormulaFamily.induction, parameter := phi }
  | ⟨_, IsPAFormulaComponent.induction_step phi⟩ =>
      { family := PAFormulaFamily.induction, parameter := phi }
  | ⟨_, IsPAFormulaComponent.induction_full phi⟩ =>
      { family := PAFormulaFamily.induction, parameter := phi }

/-- Component-level target phase. -/
def phaseOfPAFormulaComponent : PAFormulaComponent → Phase
  | ⟨_, IsPAFormulaComponent.succ_ne_zero⟩ => Phase.base
  | ⟨_, IsPAFormulaComponent.succ_injective⟩ => Phase.base
  | ⟨_, IsPAFormulaComponent.add_base⟩ => Phase.base
  | ⟨_, IsPAFormulaComponent.add_step⟩ => Phase.step
  | ⟨_, IsPAFormulaComponent.mul_base⟩ => Phase.base
  | ⟨_, IsPAFormulaComponent.mul_step⟩ => Phase.step
  | ⟨_, IsPAFormulaComponent.induction_base _phi⟩ => Phase.base
  | ⟨_, IsPAFormulaComponent.induction_step _phi⟩ => Phase.step
  | ⟨_, IsPAFormulaComponent.induction_full _phi⟩ => Phase.base

/-- Active R1 interface for formula components. -/
def I_PA_formula_component : Subfamily PAFormulaInterface
  | PAFormulaInterface.formulaTrace => True

/-- Observation map on formula components. -/
def obs_PA_formula_component :
    PAFormulaInterface → PAFormulaComponent → PAFormulaTrace
  | PAFormulaInterface.formulaTrace, c => traceOfPAFormulaComponent c

/-- Target map on formula components. -/
def sigma_PA_formula_component : PAFormulaComponent → Phase :=
  phaseOfPAFormulaComponent

/-- Component-level finite mediator. -/
def M_PA_formula_component : PAFormulaComponent → Fin 2 :=
  fun c => phaseToFin (sigma_PA_formula_component c)

/-- Canonical induction base component for `phi0`. -/
def x_pa_induction_base : PAFormulaComponent :=
  ⟨inductionBaseFormula phi0, IsPAFormulaComponent.induction_base phi0⟩

/-- Canonical induction step component for `phi0`. -/
def y_pa_induction_step : PAFormulaComponent :=
  ⟨inductionStepFormula phi0, IsPAFormulaComponent.induction_step phi0⟩

/-- Canonical formula-level induction component pair. -/
def canonicalPair_PA_formula_component :
    PAFormulaComponent × PAFormulaComponent :=
  (x_pa_induction_base, y_pa_induction_step)

/-- The target separates the canonical induction components. -/
theorem requiredAtCanonicalPair_PA_formula_component :
    RequiredDistinction sigma_PA_formula_component
      canonicalPair_PA_formula_component.1 canonicalPair_PA_formula_component.2 := by
  change Phase.base ≠ Phase.step
  exact Phase.base_ne_step

/-- R1 sees the same induction trace and same formula parameter on the pair. -/
theorem jointSameAtCanonicalPair_PA_formula_component :
    JointSame obs_PA_formula_component I_PA_formula_component
      canonicalPair_PA_formula_component.1 canonicalPair_PA_formula_component.2 := by
  intro j _hj
  cases j
  rfl

/-- The canonical pair is a residual witness on formula components. -/
theorem canonicalDiagonalWitness_PA_formula_component :
    DiagonalizationWitness
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component
      canonicalPair_PA_formula_component.1
      canonicalPair_PA_formula_component.2 :=
  ⟨requiredAtCanonicalPair_PA_formula_component,
    jointSameAtCanonicalPair_PA_formula_component⟩

/-- The component residual is nonempty. -/
theorem residualNonempty_PA_formula_component :
    ResidualNonempty_R2
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component :=
  ⟨canonicalPair_PA_formula_component.1,
    canonicalPair_PA_formula_component.2,
    canonicalDiagonalWitness_PA_formula_component⟩

/-- The component mediator separates every residual witness. -/
theorem M_PA_formula_component_separates_witnesses :
    ∀ x y : PAFormulaComponent,
      DiagonalizationWitness
        obs_PA_formula_component sigma_PA_formula_component
        I_PA_formula_component x y →
        M_PA_formula_component x ≠ M_PA_formula_component y := by
  intro x y hWitness hM
  have hPhase : sigma_PA_formula_component x = sigma_PA_formula_component y :=
    phaseToFin_injective hM
  exact hWitness.1 hPhase

/-- The component mediator closes the mediated residual. -/
theorem mediatedResidualEmpty_M_PA_formula_component :
    MediatedResidualEmpty
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component := by
  intro x y hResidual
  exact
    (M_PA_formula_component_separates_witnesses x y
      ⟨hResidual.1, hResidual.2.1⟩)
      hResidual.2.2

/-- The component mediator separates the canonical pair. -/
theorem M_PA_formula_component_separates_canonicalPair :
    M_PA_formula_component canonicalPair_PA_formula_component.1 ≠
      M_PA_formula_component canonicalPair_PA_formula_component.2 :=
by
  change phaseToFin Phase.base ≠ phaseToFin Phase.step
  exact phaseToFin_base_ne_step

/-- Any proper active subfamily omits the single formula-trace reader. -/
theorem not_mem_of_proper_formula_component_subfamily
    (K : Subfamily PAFormulaInterface) :
    Subfamily.Proper K I_PA_formula_component →
      ¬ K PAFormulaInterface.formulaTrace := by
  intro hProper
  rcases hProper.2 with ⟨j, _hIj, hNotK⟩
  cases j
  exact hNotK

/-- The canonical component pair is indistinguishable for proper subfamilies. -/
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

/-- Explicit non-descent witness for every proper active subfamily. -/
theorem witnessedIrreducibleMediator_M_PA_formula_component :
    WitnessedIrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      M_PA_formula_component := by
  intro K hProper
  exact
    ⟨canonicalPair_PA_formula_component.1,
      canonicalPair_PA_formula_component.2,
      jointSameAtCanonicalPair_formula_component_of_properSubfamily K hProper,
      M_PA_formula_component_separates_canonicalPair⟩

/-- The component mediator does not descend to any proper active subfamily. -/
theorem irreducibleMediator_M_PA_formula_component :
    IrreducibleMediator
      obs_PA_formula_component I_PA_formula_component
      M_PA_formula_component :=
  witnessedIrreducibleMediator_irreducibleMediator
    obs_PA_formula_component I_PA_formula_component M_PA_formula_component
    witnessedIrreducibleMediator_M_PA_formula_component

/-- Formula components give a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_PA_formula_component :
    ProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨residualNonempty_PA_formula_component,
    mediatedResidualEmpty_M_PA_formula_component,
    irreducibleMediator_M_PA_formula_component⟩

/-- Witnessed formula-component proper mediated R2 certificate. -/
theorem witnessedProperMediatedR2Certificate_M_PA_formula_component :
    WitnessedProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨residualNonempty_PA_formula_component,
    mediatedResidualEmpty_M_PA_formula_component,
    witnessedIrreducibleMediator_M_PA_formula_component⟩

/-- No smaller proper mediated component certificate exists below `2`. -/
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

/-- Dimension-minimal proper R2 closure for formula components. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_PA_formula_component :
    DimensionMinimalProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨properMediatedR2Certificate_M_PA_formula_component,
    no_smaller_properMediatedR2Certificate_PA_formula_component⟩

/-- Dimension-minimal witnessed proper R2 closure for formula components. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_PA_formula_component :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component M_PA_formula_component :=
  ⟨witnessedProperMediatedR2Certificate_M_PA_formula_component,
    no_smaller_properMediatedR2Certificate_PA_formula_component⟩

/-- Exact proper mediated R2 dimension for formula components. -/
theorem exactProperMediatedR2Dimension_two_PA_formula_component :
    ExactProperMediatedR2Dimension
      obs_PA_formula_component sigma_PA_formula_component
      I_PA_formula_component 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_component

/-- End-to-end formula-component package. -/
theorem endToEnd_PA_formula_component :
    ResidualNonempty_R2
        obs_PA_formula_component sigma_PA_formula_component
        I_PA_formula_component
      ∧ MediatedResidualEmpty
          obs_PA_formula_component sigma_PA_formula_component
          I_PA_formula_component M_PA_formula_component
      ∧ IrreducibleMediator
          obs_PA_formula_component I_PA_formula_component
          M_PA_formula_component
      ∧ (∀ m : Nat,
          m < 2 →
            ¬ ExistsProperMediatedR2CertificateAtDim
              obs_PA_formula_component sigma_PA_formula_component
              I_PA_formula_component m) :=
  endToEnd_staticProperMediatedR2Certificate
    obs_PA_formula_component sigma_PA_formula_component
    I_PA_formula_component M_PA_formula_component
    dimensionMinimalProperMediatedR2Certificate_M_PA_formula_component

end PeanoPAFormulaAxioms
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.Term
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.Formula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paSuccNeZeroFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paSuccInjectiveFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paAddZeroFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paAddSuccFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paMulZeroFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paMulSuccFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paInductionFormula
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.IsPAFormulaAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.PAFormulaAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paSuccNeZeroAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paSuccInjectiveAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paAddZeroAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paAddSuccAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paMulZeroAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paMulSuccAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.paInductionAxiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.canonicalDiagonalWitness_PA_formula_axiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.properMediatedR2Certificate_M_PA_formula_axiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.exactProperMediatedR2Dimension_two_PA_formula_axiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.endToEnd_PA_formula_axiom
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.IsPAFormulaComponent
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.PAFormulaComponent
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.canonicalDiagonalWitness_PA_formula_component
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.properMediatedR2Certificate_M_PA_formula_component
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.exactProperMediatedR2Dimension_two_PA_formula_component
#print axioms LocalSemanticClosure.PeanoPAFormulaAxioms.endToEnd_PA_formula_component
/- AXIOM_AUDIT_END -/
