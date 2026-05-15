import RegimesSelfContained
import FiniteDimensionHierarchy

/-!
# ZFC formula axioms

This file is the syntax-level ZFC target.

The objects are not Lean axioms and they are not informal labels.  They are
first-order syntax trees in the pure language of set theory:

* variables as terms;
* equality and membership as atomic formulas;
* propositional connectives;
* universal and existential quantification;
* the standard ZFC axiom formulas, including Separation, Replacement, and
  Choice.

The schema constructors store explicit variable-role and freshness conditions.
The R1/R2 certificate layer below is added only after these formula objects are
available, and it operates on formula-bearing ZFC objects.

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace ZFCFormulaAxioms

open Standalone.RegimesSelfContained

/-- First-order terms for the pure language of set theory. -/
inductive Term
  | var : Nat → Term
deriving DecidableEq

/-- First-order formulas for the pure language of set theory. -/
inductive Formula
  | falsum : Formula
  | equal : Term → Term → Formula
  | mem : Term → Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | iff : Formula → Formula → Formula
  | forallE : Nat → Formula → Formula
  | existsE : Nat → Formula → Formula
deriving DecidableEq

namespace Term

/-- A variable occurs in a term. -/
inductive FreeIn (target : Nat) : Term → Prop
  | var : FreeIn target (Term.var target)

/-- Substitute one variable by a term in a term. -/
def subst (target : Nat) (replacement : Term) : Term → Term
  | var n =>
      match Nat.decEq n target with
      | isTrue _ => replacement
      | isFalse _ => var n

end Term

namespace Formula

/-- A variable occurs free in a formula. -/
inductive FreeIn (target : Nat) : Formula → Prop
  | equal_left {lhs rhs : Term} :
      Term.FreeIn target lhs → FreeIn target (Formula.equal lhs rhs)
  | equal_right {lhs rhs : Term} :
      Term.FreeIn target rhs → FreeIn target (Formula.equal lhs rhs)
  | mem_left {lhs rhs : Term} :
      Term.FreeIn target lhs → FreeIn target (Formula.mem lhs rhs)
  | mem_right {lhs rhs : Term} :
      Term.FreeIn target rhs → FreeIn target (Formula.mem lhs rhs)
  | not {p : Formula} :
      FreeIn target p → FreeIn target (Formula.not p)
  | and_left {p q : Formula} :
      FreeIn target p → FreeIn target (Formula.and p q)
  | and_right {p q : Formula} :
      FreeIn target q → FreeIn target (Formula.and p q)
  | or_left {p q : Formula} :
      FreeIn target p → FreeIn target (Formula.or p q)
  | or_right {p q : Formula} :
      FreeIn target q → FreeIn target (Formula.or p q)
  | imp_left {p q : Formula} :
      FreeIn target p → FreeIn target (Formula.imp p q)
  | imp_right {p q : Formula} :
      FreeIn target q → FreeIn target (Formula.imp p q)
  | iff_left {p q : Formula} :
      FreeIn target p → FreeIn target (Formula.iff p q)
  | iff_right {p q : Formula} :
      FreeIn target q → FreeIn target (Formula.iff p q)
  | forallE {bound : Nat} {p : Formula} :
      target ≠ bound → FreeIn target p → FreeIn target (Formula.forallE bound p)
  | existsE {bound : Nat} {p : Formula} :
      target ≠ bound → FreeIn target p → FreeIn target (Formula.existsE bound p)

/--
Substitute a term for one named free variable in a formula.

If the same variable is bound by a quantifier, substitution stops under that
binder.
-/
def subst (target : Nat) (replacement : Term) : Formula → Formula
  | falsum => falsum
  | equal lhs rhs =>
      equal (Term.subst target replacement lhs)
        (Term.subst target replacement rhs)
  | mem lhs rhs =>
      mem (Term.subst target replacement lhs)
        (Term.subst target replacement rhs)
  | not p => not (subst target replacement p)
  | and p q => and (subst target replacement p) (subst target replacement q)
  | or p q => or (subst target replacement p) (subst target replacement q)
  | imp p q => imp (subst target replacement p) (subst target replacement q)
  | iff p q => iff (subst target replacement p) (subst target replacement q)
  | forallE n p =>
      match Nat.decEq n target with
      | isTrue _ => forallE n p
      | isFalse _ => forallE n (subst target replacement p)
  | existsE n p =>
      match Nat.decEq n target with
      | isTrue _ => existsE n p
      | isFalse _ => existsE n (subst target replacement p)

end Formula

/-- Variable term. -/
def v (n : Nat) : Term :=
  Term.var n

/-- Syntactic inequality. -/
def neq (lhs rhs : Term) : Formula :=
  Formula.not (Formula.equal lhs rhs)

/-- Syntactic non-membership. -/
def notMem (lhs rhs : Term) : Formula :=
  Formula.not (Formula.mem lhs rhs)

/-- `subset x y` expanded as `forall z, z in x -> z in y`. -/
def subset (elem : Nat) (x y : Term) : Formula :=
  Formula.forallE elem
    (Formula.imp
      (Formula.mem (v elem) x)
      (Formula.mem (v elem) y))

/-- `x` is empty, expanded as `forall z, z notin x`. -/
def emptyPred (elem : Nat) (x : Term) : Formula :=
  Formula.forallE elem
    (notMem (v elem) x)

/-- `s` is the von Neumann successor of `y`. -/
def successorPred (elem : Nat) (y s : Term) : Formula :=
  Formula.forallE elem
    (Formula.iff
      (Formula.mem (v elem) s)
      (Formula.or
        (Formula.mem (v elem) y)
        (Formula.equal (v elem) y)))

/-- `exists unique x, p`, where uniqueness is expanded syntactically. -/
def existsUnique (x x' : Nat) (p : Formula) : Formula :=
  Formula.existsE x
    (Formula.and p
      (Formula.forallE x'
        (Formula.imp
          (Formula.subst x (v x') p)
          (Formula.equal (v x') (v x)))))

/-- All listed variables are required to be pairwise distinct. -/
def PairwiseDistinct : List Nat → Prop
  | [] => True
  | x :: xs => (∀ y : Nat, y ∈ xs → x ≠ y) ∧ PairwiseDistinct xs

/-- Explicit distinctness evidence for three variable roles. -/
structure RoleVarsDistinct3 (a b c : Nat) where
  a_ne_b : a ≠ b
  a_ne_c : a ≠ c
  b_ne_c : b ≠ c

/-- Explicit distinctness evidence for five variable roles. -/
structure RoleVarsDistinct5 (a b c d e : Nat) where
  a_ne_b : a ≠ b
  a_ne_c : a ≠ c
  a_ne_d : a ≠ d
  a_ne_e : a ≠ e
  b_ne_c : b ≠ c
  b_ne_d : b ≠ d
  b_ne_e : b ≠ e
  c_ne_d : c ≠ d
  c_ne_e : c ≠ e
  d_ne_e : d ≠ e

/-- Side conditions for the Separation schema. -/
structure SeparationSideConditions (phi : Formula)
    (a b x : Nat) (params : List Nat) where
  b_not_free_in_phi : ¬ Formula.FreeIn b phi
  role_vars_distinct : RoleVarsDistinct3 a b x
  params_distinct_from_subset : ∀ p : Nat, p ∈ params → p ≠ b

/-- Variable-role data for the Separation schema. -/
structure SeparationData (phi : Formula) where
  a : Nat
  b : Nat
  x : Nat
  params : List Nat
  side : SeparationSideConditions phi a b x params

/-- Side conditions for the Replacement schema. -/
structure ReplacementSideConditions (phi : Formula)
    (a b x y y' : Nat) (params : List Nat) where
  b_not_free_in_phi : ¬ Formula.FreeIn b phi
  y'_not_free_in_phi : ¬ Formula.FreeIn y' phi
  role_vars_distinct : RoleVarsDistinct5 a b x y y'
  params_distinct_from_image : ∀ p : Nat, p ∈ params → p ≠ b
  params_distinct_from_unique_bound : ∀ p : Nat, p ∈ params → p ≠ y'

/-- Variable-role data for the Replacement schema. -/
structure ReplacementData (phi : Formula) where
  a : Nat
  b : Nat
  x : Nat
  y : Nat
  y' : Nat
  params : List Nat
  side : ReplacementSideConditions phi a b x y y' params

/-- ZFC axiom families. -/
inductive AxiomFamily
  | extensionality
  | empty_set
  | pairing
  | union
  | power_set
  | infinity
  | separation
  | replacement
  | foundation
  | choice
deriving DecidableEq

/-- Formula-component roles used by the R1/R2 certificates below. -/
inductive ZFCComponentRole
  | full_axiom
  | schema_parameter
deriving DecidableEq

/-- `forall x y, (forall z, z in x <-> z in y) -> x = y`. -/
def zfcExtensionalityFormula : Formula :=
  Formula.forallE 0
    (Formula.forallE 1
      (Formula.imp
        (Formula.forallE 2
          (Formula.iff
            (Formula.mem (v 2) (v 0))
            (Formula.mem (v 2) (v 1))))
        (Formula.equal (v 0) (v 1))))

/-- `exists x, forall z, z notin x`. -/
def zfcEmptySetFormula : Formula :=
  Formula.existsE 0
    (emptyPred 1 (v 0))

/-- `forall a b, exists p, forall z, z in p <-> (z = a or z = b)`. -/
def zfcPairingFormula : Formula :=
  Formula.forallE 0
    (Formula.forallE 1
      (Formula.existsE 2
        (Formula.forallE 3
          (Formula.iff
            (Formula.mem (v 3) (v 2))
            (Formula.or
              (Formula.equal (v 3) (v 0))
              (Formula.equal (v 3) (v 1)))))))

/-- `forall x, exists u, forall z, z in u <-> exists y, z in y and y in x`. -/
def zfcUnionFormula : Formula :=
  Formula.forallE 0
    (Formula.existsE 1
      (Formula.forallE 2
        (Formula.iff
          (Formula.mem (v 2) (v 1))
          (Formula.existsE 3
            (Formula.and
              (Formula.mem (v 2) (v 3))
              (Formula.mem (v 3) (v 0)))))))

/-- `forall x, exists p, forall z, z in p <-> z subset x`. -/
def zfcPowerSetFormula : Formula :=
  Formula.forallE 0
    (Formula.existsE 1
      (Formula.forallE 2
        (Formula.iff
          (Formula.mem (v 2) (v 1))
          (subset 3 (v 2) (v 0)))))

/--
Infinity, expanded without primitive empty-set or successor symbols.

`exists x, (exists e, empty(e) and e in x) and
forall y, y in x -> exists s, successor(y,s) and s in x`.
-/
def zfcInfinityFormula : Formula :=
  Formula.existsE 0
    (Formula.and
      (Formula.existsE 1
        (Formula.and
          (emptyPred 2 (v 1))
          (Formula.mem (v 1) (v 0))))
      (Formula.forallE 3
        (Formula.imp
          (Formula.mem (v 3) (v 0))
          (Formula.existsE 4
            (Formula.and
              (successorPred 5 (v 3) (v 4))
              (Formula.mem (v 4) (v 0)))))))

/-- Separation schema formula for the formula and variable-role data. -/
def zfcSeparationFormula (phi : Formula) (data : SeparationData phi) : Formula :=
  Formula.forallE data.a
    (Formula.existsE data.b
      (Formula.forallE data.x
        (Formula.iff
          (Formula.mem (v data.x) (v data.b))
          (Formula.and
            (Formula.mem (v data.x) (v data.a))
            phi))))

/-- Functional premise for a Replacement instance. -/
def replacementFunctionalPremise
    (phi : Formula) (data : ReplacementData phi) : Formula :=
  Formula.forallE data.x
    (Formula.imp
      (Formula.mem (v data.x) (v data.a))
      (Formula.existsE data.y
        (Formula.and phi
          (Formula.forallE data.y'
            (Formula.imp
              (Formula.subst data.y (v data.y') phi)
              (Formula.equal (v data.y') (v data.y)))))))

/-- Image-set conclusion for a Replacement instance. -/
def replacementImageConclusion
    (phi : Formula) (data : ReplacementData phi) : Formula :=
  Formula.existsE data.b
    (Formula.forallE data.y
      (Formula.iff
        (Formula.mem (v data.y) (v data.b))
        (Formula.existsE data.x
          (Formula.and
            (Formula.mem (v data.x) (v data.a))
            phi))))

/-- Replacement schema formula for the formula and variable-role data. -/
def zfcReplacementFormula (phi : Formula) (data : ReplacementData phi) : Formula :=
  Formula.forallE data.a
    (Formula.imp
      (replacementFunctionalPremise phi data)
      (replacementImageConclusion phi data))

/--
Foundation, written without a primitive empty set:

`forall x, (exists z, z in x) -> exists y, y in x and
forall z, z in y -> z notin x`.
-/
def zfcFoundationFormula : Formula :=
  Formula.forallE 0
    (Formula.imp
      (Formula.existsE 1
        (Formula.mem (v 1) (v 0)))
      (Formula.existsE 2
        (Formula.and
          (Formula.mem (v 2) (v 0))
          (Formula.forallE 3
            (Formula.imp
              (Formula.mem (v 3) (v 2))
              (notMem (v 3) (v 0)))))))

/-- Every member of `x` is nonempty. -/
def choiceNonemptyMembers (x y z : Nat) : Formula :=
  Formula.forallE y
    (Formula.imp
      (Formula.mem (v y) (v x))
      (Formula.existsE z
        (Formula.mem (v z) (v y))))

/-- Members of `x` are pairwise disjoint. -/
def choicePairwiseDisjoint (x y z w : Nat) : Formula :=
  Formula.forallE y
    (Formula.forallE z
      (Formula.imp
        (Formula.mem (v y) (v x))
        (Formula.imp
          (Formula.mem (v z) (v x))
          (Formula.imp
            (neq (v y) (v z))
            (Formula.not
              (Formula.existsE w
                (Formula.and
                  (Formula.mem (v w) (v y))
                  (Formula.mem (v w) (v z)))))))))

/-- The choice set `c` is contained in the union of the family `x`. -/
def choiceSetContainedInUnion (x c u y : Nat) : Formula :=
  Formula.forallE u
    (Formula.imp
      (Formula.mem (v u) (v c))
      (Formula.existsE y
        (Formula.and
          (Formula.mem (v y) (v x))
          (Formula.mem (v u) (v y)))))

/-- The choice set has exactly one element in every member of the family. -/
def choiceSelectsUniquely (x c y u v' : Nat) : Formula :=
  Formula.forallE y
    (Formula.imp
      (Formula.mem (v y) (v x))
      (Formula.existsE u
        (Formula.and
          (Formula.mem (v u) (v y))
          (Formula.and
            (Formula.mem (v u) (v c))
            (Formula.forallE v'
              (Formula.imp
                (Formula.and
                  (Formula.mem (v v') (v y))
                  (Formula.mem (v v') (v c)))
                (Formula.equal (v v') (v u))))))))

/--
Choice, as: every set of nonempty pairwise disjoint sets has a choice set.

The choice set is additionally required to be contained in the union of the
family.
-/
def zfcChoiceFormula : Formula :=
  Formula.forallE 0
    (Formula.imp
      (Formula.and
        (choiceNonemptyMembers 0 1 2)
        (choicePairwiseDisjoint 0 3 4 5))
      (Formula.existsE 6
        (Formula.and
          (choiceSetContainedInUnion 0 6 7 8)
          (choiceSelectsUniquely 0 6 9 10 11))))

/--
Witness that a formula is one of the standard ZFC axiom formulas or a schema
instance.
-/
inductive IsZFCFormulaAxiom : Formula → Type
  | extensionality : IsZFCFormulaAxiom zfcExtensionalityFormula
  | empty_set : IsZFCFormulaAxiom zfcEmptySetFormula
  | pairing : IsZFCFormulaAxiom zfcPairingFormula
  | union : IsZFCFormulaAxiom zfcUnionFormula
  | power_set : IsZFCFormulaAxiom zfcPowerSetFormula
  | infinity : IsZFCFormulaAxiom zfcInfinityFormula
  | separation (phi : Formula) (data : SeparationData phi) :
      IsZFCFormulaAxiom (zfcSeparationFormula phi data)
  | replacement (phi : Formula) (data : ReplacementData phi) :
      IsZFCFormulaAxiom (zfcReplacementFormula phi data)
  | foundation : IsZFCFormulaAxiom zfcFoundationFormula
  | choice : IsZFCFormulaAxiom zfcChoiceFormula

/-- A ZFC axiom as an actual formula together with its syntactic certificate. -/
structure ZFCFormulaAxiom where
  formula : Formula
  witness : IsZFCFormulaAxiom formula

/-- The ZFC extensionality axiom formula. -/
def zfcExtensionalityAxiom : ZFCFormulaAxiom :=
  ⟨zfcExtensionalityFormula, IsZFCFormulaAxiom.extensionality⟩

/-- The ZFC empty-set axiom formula. -/
def zfcEmptySetAxiom : ZFCFormulaAxiom :=
  ⟨zfcEmptySetFormula, IsZFCFormulaAxiom.empty_set⟩

/-- The ZFC pairing axiom formula. -/
def zfcPairingAxiom : ZFCFormulaAxiom :=
  ⟨zfcPairingFormula, IsZFCFormulaAxiom.pairing⟩

/-- The ZFC union axiom formula. -/
def zfcUnionAxiom : ZFCFormulaAxiom :=
  ⟨zfcUnionFormula, IsZFCFormulaAxiom.union⟩

/-- The ZFC power-set axiom formula. -/
def zfcPowerSetAxiom : ZFCFormulaAxiom :=
  ⟨zfcPowerSetFormula, IsZFCFormulaAxiom.power_set⟩

/-- The ZFC infinity axiom formula. -/
def zfcInfinityAxiom : ZFCFormulaAxiom :=
  ⟨zfcInfinityFormula, IsZFCFormulaAxiom.infinity⟩

/-- A ZFC Separation schema instance. -/
def zfcSeparationAxiom (phi : Formula) (data : SeparationData phi) :
    ZFCFormulaAxiom :=
  ⟨zfcSeparationFormula phi data, IsZFCFormulaAxiom.separation phi data⟩

/-- A ZFC Replacement schema instance. -/
def zfcReplacementAxiom (phi : Formula) (data : ReplacementData phi) :
    ZFCFormulaAxiom :=
  ⟨zfcReplacementFormula phi data, IsZFCFormulaAxiom.replacement phi data⟩

/-- The ZFC foundation axiom formula. -/
def zfcFoundationAxiom : ZFCFormulaAxiom :=
  ⟨zfcFoundationFormula, IsZFCFormulaAxiom.foundation⟩

/-- The ZFC choice axiom formula. -/
def zfcChoiceAxiom : ZFCFormulaAxiom :=
  ⟨zfcChoiceFormula, IsZFCFormulaAxiom.choice⟩

/-- A formula component used by the R1/R2 certificates below. -/
structure ZFCFormulaComponent where
  formula : Formula
  family : AxiomFamily
  role : ZFCComponentRole

/-!
## R1/R2 finite parameter-coordinate certificate

For every `n >= 2`, the following sections build actual ZFC formula
components from Separation and Replacement schema instances.

Each state carries a real `Formula`.  The R1 projection reads the ZFC family
and component role, but not the parameter coordinate.  The R2 target reads the
finite parameter coordinate.  The exact lower bound is proved by reducing any
smaller mediated closure to an impossible injection `Fin n -> Fin m`.
-/

/-- Formula parameter used by the finite ZFC component family. -/
def zfcParameterPhi (i : Nat) : Formula :=
  Formula.equal (v 2) (v (3 + i))

/-- A free occurrence in a variable term identifies the variable. -/
theorem termFreeIn_var_eq {target n : Nat} :
    Term.FreeIn target (Term.var n) → target = n := by
  intro h
  cases h
  rfl

/-- `1` and `2` are distinct variable indices. -/
theorem one_ne_two : (1 : Nat) ≠ 2 := by
  intro h
  have hZeroOne : (0 : Nat) = 1 := Nat.succ.inj h
  cases hZeroOne

/-- The parameter variable `3 + i` is not the subset variable `1`. -/
theorem parameterVar_ne_one (i : Nat) :
    3 + i ≠ 1 := by
  have hOneLtThree : 1 < 3 :=
    Nat.succ_lt_succ (Nat.succ_pos 1)
  have hThreeLe : 3 ≤ 3 + i := Nat.le_add_right 3 i
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hOneLtThree hThreeLe)

/-- Membership in a singleton list identifies the element. -/
theorem mem_singleton_eq {p q : Nat} :
    p ∈ [q] → p = q := by
  intro h
  cases h with
  | head =>
      rfl
  | tail _ hTail =>
      cases hTail

/-- Variable `1` is not free in the parameter formula. -/
theorem one_not_free_zfcParameterPhi (i : Nat) :
    ¬ Formula.FreeIn 1 (zfcParameterPhi i) := by
  intro h
  unfold zfcParameterPhi at h
  cases h with
  | equal_left ht =>
      exact one_ne_two (termFreeIn_var_eq ht)
  | equal_right ht =>
      exact parameterVar_ne_one i (termFreeIn_var_eq ht).symm

/-- The role variables used by the finite Separation instances are distinct. -/
def roleVarsDistinct_zero_one_two :
    RoleVarsDistinct3 0 1 2 :=
  { a_ne_b := by
      intro h
      cases h
    a_ne_c := by
      intro h
      cases h
    b_ne_c := one_ne_two }

/-- Side conditions for the finite Separation instance at coordinate `i`. -/
def zfcParameterSeparationSide (i : Nat) :
    SeparationSideConditions (zfcParameterPhi i) 0 1 2 [3 + i] :=
  { b_not_free_in_phi := one_not_free_zfcParameterPhi i
    role_vars_distinct := roleVarsDistinct_zero_one_two
    params_distinct_from_subset := by
      intro p hp
      have hpEq : p = 3 + i := mem_singleton_eq hp
      rw [hpEq]
      exact parameterVar_ne_one i }

/-- Variable-role data for the finite Separation instance at coordinate `i`. -/
def zfcParameterSeparationData (i : Nat) :
    SeparationData (zfcParameterPhi i) :=
  { a := 0
    b := 1
    x := 2
    params := [3 + i]
    side := zfcParameterSeparationSide i }

/-- The actual Separation axiom formula used at finite coordinate `i`. -/
def zfcParameterSeparationFormula (i : Nat) : Formula :=
  zfcSeparationFormula (zfcParameterPhi i)
    (zfcParameterSeparationData i)

/-- The certified ZFC Separation axiom at finite coordinate `i`. -/
def zfcParameterSeparationAxiom (i : Nat) : ZFCFormulaAxiom :=
  zfcSeparationAxiom (zfcParameterPhi i)
    (zfcParameterSeparationData i)

/-- Formula component at finite parameter coordinate `i`. -/
def zfcParameterFormulaComponent (i : Nat) : ZFCFormulaComponent :=
  { formula := zfcParameterSeparationFormula i
    family := AxiomFamily.separation
    role := ZFCComponentRole.schema_parameter }

/-- Formula parameter used by the finite ZFC Replacement component family. -/
def zfcReplacementParameterPhi (i : Nat) : Formula :=
  Formula.equal (v 2) (v (5 + i))

/-- `4` and `2` are distinct variable indices. -/
theorem four_ne_two : (4 : Nat) ≠ 2 := by
  decide

/-- The Replacement parameter variable `5 + i` is not the image variable `1`. -/
theorem replacementParameterVar_ne_one (i : Nat) :
    5 + i ≠ 1 := by
  have hOneLtFive : 1 < 5 := by
    decide
  have hFiveLe : 5 ≤ 5 + i := Nat.le_add_right 5 i
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hOneLtFive hFiveLe)

/-- The Replacement parameter variable `5 + i` is not the uniqueness variable `4`. -/
theorem replacementParameterVar_ne_four (i : Nat) :
    5 + i ≠ 4 := by
  have hFourLtFive : 4 < 5 := by
    decide
  have hFiveLe : 5 ≤ 5 + i := Nat.le_add_right 5 i
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hFourLtFive hFiveLe)

/-- Variable `1` is not free in the Replacement parameter formula. -/
theorem one_not_free_zfcReplacementParameterPhi (i : Nat) :
    ¬ Formula.FreeIn 1 (zfcReplacementParameterPhi i) := by
  intro h
  unfold zfcReplacementParameterPhi at h
  cases h with
  | equal_left ht =>
      exact one_ne_two (termFreeIn_var_eq ht)
  | equal_right ht =>
      exact replacementParameterVar_ne_one i (termFreeIn_var_eq ht).symm

/-- Variable `4` is not free in the Replacement parameter formula. -/
theorem four_not_free_zfcReplacementParameterPhi (i : Nat) :
    ¬ Formula.FreeIn 4 (zfcReplacementParameterPhi i) := by
  intro h
  unfold zfcReplacementParameterPhi at h
  cases h with
  | equal_left ht =>
      exact four_ne_two (termFreeIn_var_eq ht)
  | equal_right ht =>
      exact replacementParameterVar_ne_four i (termFreeIn_var_eq ht).symm

/-- The role variables used by the finite Replacement instances are distinct. -/
def roleVarsDistinct_zero_one_two_three_four :
    RoleVarsDistinct5 0 1 2 3 4 :=
  { a_ne_b := by decide
    a_ne_c := by decide
    a_ne_d := by decide
    a_ne_e := by decide
    b_ne_c := by decide
    b_ne_d := by decide
    b_ne_e := by decide
    c_ne_d := by decide
    c_ne_e := by decide
    d_ne_e := by decide }

/-- Side conditions for the finite Replacement instance at coordinate `i`. -/
def zfcParameterReplacementSide (i : Nat) :
    ReplacementSideConditions (zfcReplacementParameterPhi i) 0 1 2 3 4 [5 + i] :=
  { b_not_free_in_phi := one_not_free_zfcReplacementParameterPhi i
    y'_not_free_in_phi := four_not_free_zfcReplacementParameterPhi i
    role_vars_distinct := roleVarsDistinct_zero_one_two_three_four
    params_distinct_from_image := by
      intro p hp
      have hpEq : p = 5 + i := mem_singleton_eq hp
      rw [hpEq]
      exact replacementParameterVar_ne_one i
    params_distinct_from_unique_bound := by
      intro p hp
      have hpEq : p = 5 + i := mem_singleton_eq hp
      rw [hpEq]
      exact replacementParameterVar_ne_four i }

/-- Variable-role data for the finite Replacement instance at coordinate `i`. -/
def zfcParameterReplacementData (i : Nat) :
    ReplacementData (zfcReplacementParameterPhi i) :=
  { a := 0
    b := 1
    x := 2
    y := 3
    y' := 4
    params := [5 + i]
    side := zfcParameterReplacementSide i }

/-- The actual Replacement axiom formula used at finite coordinate `i`. -/
def zfcParameterReplacementFormula (i : Nat) : Formula :=
  zfcReplacementFormula (zfcReplacementParameterPhi i)
    (zfcParameterReplacementData i)

/-- The certified ZFC Replacement axiom at finite coordinate `i`. -/
def zfcParameterReplacementAxiom (i : Nat) : ZFCFormulaAxiom :=
  zfcReplacementAxiom (zfcReplacementParameterPhi i)
    (zfcParameterReplacementData i)

/-- Replacement formula component at finite parameter coordinate `i`. -/
def zfcReplacementParameterFormulaComponent (i : Nat) : ZFCFormulaComponent :=
  { formula := zfcParameterReplacementFormula i
    family := AxiomFamily.replacement
    role := ZFCComponentRole.schema_parameter }

/--
Finite ZFC schema-parameter states.

The finite coordinate is not attached to an arbitrary component.  Each
constructor determines the actual ZFC formula component from its coordinate.
-/
inductive ZFCFiniteParameterComponent (n : Nat)
  | separation : Fin n → ZFCFiniteParameterComponent n
  | replacement : Fin n → ZFCFiniteParameterComponent n

/-- The coordinate carried internally by a finite schema-parameter state. -/
def coordinateOfZFCFiniteParameterComponent {n : Nat}
    (s : ZFCFiniteParameterComponent n) : Fin n :=
  match s with
  | ZFCFiniteParameterComponent.separation i => i
  | ZFCFiniteParameterComponent.replacement i => i

/-- The actual formula component determined by a finite schema-parameter state. -/
def componentOfZFCFiniteParameterComponent {n : Nat}
    (s : ZFCFiniteParameterComponent n) : ZFCFormulaComponent :=
  match s with
  | ZFCFiniteParameterComponent.separation i =>
      zfcParameterFormulaComponent i.val
  | ZFCFiniteParameterComponent.replacement i =>
      zfcReplacementParameterFormulaComponent i.val

/-- The actual formula determined by a finite schema-parameter state. -/
def formulaOfZFCFiniteParameterComponent {n : Nat}
    (s : ZFCFiniteParameterComponent n) : Formula :=
  (componentOfZFCFiniteParameterComponent s).formula

/-- The canonical ZFC component at coordinate `i : Fin n`. -/
def zfcFiniteParameterComponent {n : Nat}
    (i : Fin n) : ZFCFiniteParameterComponent n :=
  ZFCFiniteParameterComponent.separation i

/-- The canonical ZFC Replacement component at coordinate `i : Fin n`. -/
def zfcFiniteReplacementParameterComponent {n : Nat}
    (i : Fin n) : ZFCFiniteParameterComponent n :=
  ZFCFiniteParameterComponent.replacement i

/-- R1 trace for finite ZFC parameter components. -/
structure ZFCFiniteTrace where
  family : AxiomFamily
  role : ZFCComponentRole
deriving DecidableEq

/-- The singleton interface for the finite ZFC certificate. -/
inductive ZFCFiniteInterface
  | componentTrace
deriving DecidableEq

/-- Active R1 family for the finite ZFC certificate. -/
def I_ZFC_finite : Subfamily ZFCFiniteInterface
  | ZFCFiniteInterface.componentTrace => True

/--
R1 observation on ZFC formula components.

It reads the ZFC axiom family and component role.  It does not read the exact
formula object and it does not read the finite parameter coordinate.
-/
def obs_ZFC_finite {n : Nat} :
    ZFCFiniteInterface → ZFCFiniteParameterComponent n → ZFCFiniteTrace
  | ZFCFiniteInterface.componentTrace, s =>
      { family := (componentOfZFCFiniteParameterComponent s).family
        role := (componentOfZFCFiniteParameterComponent s).role }

/-- R2 target: the finite parameter coordinate. -/
def sigma_ZFC_finite {n : Nat}
    (s : ZFCFiniteParameterComponent n) : Fin n :=
  coordinateOfZFCFiniteParameterComponent s

/-- Mediator: the same finite parameter coordinate. -/
def M_ZFC_finite {n : Nat}
    (s : ZFCFiniteParameterComponent n) : Fin n :=
  coordinateOfZFCFiniteParameterComponent s

/-- The first finite coordinate, available when `1 < n`. -/
def zfcFirstCoordinate {n : Nat} (h : 1 < n) : Fin n :=
  ⟨0, Nat.lt_trans Nat.zero_lt_one h⟩

/-- The second finite coordinate, available when `1 < n`. -/
def zfcSecondCoordinate {n : Nat} (h : 1 < n) : Fin n :=
  ⟨1, h⟩

/-- The first and second finite coordinates are distinct. -/
theorem zfcFirstCoordinate_ne_secondCoordinate
    {n : Nat} (h : 1 < n) :
    zfcFirstCoordinate h ≠ zfcSecondCoordinate h := by
  intro hEq
  have hVal : (0 : Nat) = 1 := congrArg Fin.val hEq
  cases hVal

/-- The first canonical ZFC finite component. -/
def x_ZFC_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n :=
  zfcFiniteParameterComponent (zfcFirstCoordinate h)

/-- The second canonical ZFC finite component. -/
def y_ZFC_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n :=
  zfcFiniteParameterComponent (zfcSecondCoordinate h)

/-- The canonical ZFC finite pair. -/
def canonicalPair_ZFC_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n × ZFCFiniteParameterComponent n :=
  (x_ZFC_finite h, y_ZFC_finite h)

/--
All canonical finite ZFC parameter components have the same R1 trace.

They all carry Separation schema parameter components.  The R1 trace does not
read the finite parameter coordinate.
-/
theorem jointSame_zfcFiniteParameterComponents
    {n : Nat} (i j : Fin n) :
    JointSame (obs_ZFC_finite (n := n)) I_ZFC_finite
      (zfcFiniteParameterComponent i)
      (zfcFiniteParameterComponent j) := by
  intro k _hk
  cases k
  rfl

/-- The canonical pair is separated by the R2 target. -/
theorem requiredAtCanonicalPair_ZFC_finite
    {n : Nat} (h : 1 < n) :
    RequiredDistinction (sigma_ZFC_finite (n := n))
      (canonicalPair_ZFC_finite h).1
      (canonicalPair_ZFC_finite h).2 := by
  exact zfcFirstCoordinate_ne_secondCoordinate h

/-- The canonical pair has the same R1 observation. -/
theorem jointSameAtCanonicalPair_ZFC_finite
    {n : Nat} (h : 1 < n) :
    JointSame (obs_ZFC_finite (n := n)) I_ZFC_finite
      (canonicalPair_ZFC_finite h).1
      (canonicalPair_ZFC_finite h).2 := by
  exact jointSame_zfcFiniteParameterComponents
    (zfcFirstCoordinate h) (zfcSecondCoordinate h)

/-- The canonical pair is a ZFC formula-component diagonal witness. -/
theorem canonicalDiagonalWitness_ZFC_finite
    {n : Nat} (h : 1 < n) :
    DiagonalizationWitness
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite
      (canonicalPair_ZFC_finite h).1
      (canonicalPair_ZFC_finite h).2 :=
  ⟨requiredAtCanonicalPair_ZFC_finite h,
    jointSameAtCanonicalPair_ZFC_finite h⟩

/-- The finite ZFC formula-component residual is nonempty. -/
theorem residualNonempty_ZFC_finite
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite :=
  ⟨(canonicalPair_ZFC_finite h).1,
    (canonicalPair_ZFC_finite h).2,
    canonicalDiagonalWitness_ZFC_finite h⟩

/-- The finite ZFC mediator closes every mediated residual. -/
theorem mediatedResidualEmpty_M_ZFC_finite
    {n : Nat} :
    MediatedResidualEmpty
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) := by
  intro x y hResidual
  exact hResidual.1 hResidual.2.2

/-- The finite ZFC mediator separates the canonical pair. -/
theorem M_ZFC_finite_separates_canonicalPair
    {n : Nat} (h : 1 < n) :
    M_ZFC_finite (canonicalPair_ZFC_finite h).1 ≠
      M_ZFC_finite (canonicalPair_ZFC_finite h).2 :=
  zfcFirstCoordinate_ne_secondCoordinate h

/-- A proper subfamily omits the single component-trace interface. -/
theorem not_mem_of_proper_ZFC_finite_subfamily
    (K : Subfamily ZFCFiniteInterface) :
    Subfamily.Proper K I_ZFC_finite →
      ¬ K ZFCFiniteInterface.componentTrace := by
  intro hProper
  rcases hProper.2 with ⟨j, _hjI, hjNotK⟩
  cases j
  exact hjNotK

/-- The canonical pair is indistinguishable for every proper active subfamily. -/
theorem jointSameAtCanonicalPair_ZFC_finite_of_properSubfamily
    {n : Nat} (h : 1 < n)
    (K : Subfamily ZFCFiniteInterface)
    (hProper : Subfamily.Proper K I_ZFC_finite) :
    JointSame (obs_ZFC_finite (n := n)) K
      (canonicalPair_ZFC_finite h).1
      (canonicalPair_ZFC_finite h).2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_ZFC_finite_subfamily K hProper) hj)

/-- Explicit non-descent witness for every proper active subfamily. -/
theorem witnessedIrreducibleMediator_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    WitnessedIrreducibleMediator
      (obs_ZFC_finite (n := n)) I_ZFC_finite
      (M_ZFC_finite (n := n)) := by
  intro K hProper
  exact
    ⟨(canonicalPair_ZFC_finite h).1,
      (canonicalPair_ZFC_finite h).2,
      jointSameAtCanonicalPair_ZFC_finite_of_properSubfamily h K hProper,
      M_ZFC_finite_separates_canonicalPair h⟩

/-- The finite ZFC mediator is irreducible. -/
theorem irreducibleMediator_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    IrreducibleMediator
      (obs_ZFC_finite (n := n)) I_ZFC_finite
      (M_ZFC_finite (n := n)) :=
  witnessedIrreducibleMediator_irreducibleMediator
    (obs_ZFC_finite (n := n)) I_ZFC_finite
    (M_ZFC_finite (n := n))
    (witnessedIrreducibleMediator_M_ZFC_finite h)

/-- The finite ZFC formula components give a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    ProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨residualNonempty_ZFC_finite h,
    mediatedResidualEmpty_M_ZFC_finite,
    irreducibleMediator_M_ZFC_finite h⟩

/-- Witnessed proper mediated R2 certificate for finite ZFC formula components. -/
theorem witnessedProperMediatedR2Certificate_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    WitnessedProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨residualNonempty_ZFC_finite h,
    mediatedResidualEmpty_M_ZFC_finite,
    witnessedIrreducibleMediator_M_ZFC_finite h⟩

/--
Any mediated closure for the finite ZFC parameter-coordinate family induces an
injection from `Fin n` into the mediator codomain.
-/
theorem injective_of_mediatedResidualEmpty_ZFC_finite
    {n m : Nat} {M : ZFCFiniteParameterComponent n → Fin m} :
    MediatedResidualEmpty
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite M →
        Function.Injective
          (fun i : Fin n => M (zfcFiniteParameterComponent i)) := by
  intro hCloses i j hM
  by_cases hij : i = j
  · exact hij
  · have hReq :
        RequiredDistinction (sigma_ZFC_finite (n := n))
          (zfcFiniteParameterComponent i)
          (zfcFiniteParameterComponent j) := by
      intro hSigma
      exact hij hSigma
    have hResidual :
        MediatedResidual
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite M
          (zfcFiniteParameterComponent i)
          (zfcFiniteParameterComponent j) :=
      ⟨hReq, ⟨jointSame_zfcFiniteParameterComponents i j, hM⟩⟩
    exact False.elim
      (hCloses
        (zfcFiniteParameterComponent i)
        (zfcFiniteParameterComponent j)
        hResidual)

/-- No smaller proper mediated certificate can close the finite ZFC family. -/
theorem no_smaller_properMediatedR2Certificate_ZFC_finite
    {n : Nat} :
    ∀ m : Nat,
      m < n →
        ¬ ExistsProperMediatedR2CertificateAtDim
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (zfcFiniteParameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_finite hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm (fun i : Fin n => M (zfcFiniteParameterComponent i)))
      hInjective

/-- No smaller mediated certificate can close the finite ZFC family. -/
theorem no_smaller_mediatedR2Certificate_ZFC_finite
    {n : Nat} :
    ∀ m : Nat,
      m < n →
        ¬ ExistsMediatedR2CertificateAtDim
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (zfcFiniteParameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_finite hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm (fun i : Fin n => M (zfcFiniteParameterComponent i)))
      hInjective

/-- The finite ZFC mediator realizes dimension-minimal R2 closure. -/
theorem dimensionMinimalMediatedR2Certificate_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨properMediatedR2Certificate.toMediatedR2Certificate
      (properMediatedR2Certificate_M_ZFC_finite h),
    no_smaller_mediatedR2Certificate_ZFC_finite⟩

/-- The finite ZFC mediator realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨properMediatedR2Certificate_M_ZFC_finite h,
    no_smaller_properMediatedR2Certificate_ZFC_finite⟩

/-- The finite ZFC mediator realizes witnessed dimension-minimal closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨witnessedProperMediatedR2Certificate_M_ZFC_finite h,
    no_smaller_properMediatedR2Certificate_ZFC_finite⟩

/--
For every `n >= 2`, the finite ZFC formula-component family has exact
mediated R2 dimension `n`.
-/
theorem exactMediatedR2Dimension_n_ZFC_finite
    {n : Nat} (h : 1 < n) :
    ExactMediatedR2Dimension
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite n :=
  exactMediatedR2Dimension_of_dimensionMinimalCertificate
    (dimensionMinimalMediatedR2Certificate_M_ZFC_finite h)

/--
For every `n >= 2`, the finite ZFC formula-component family has exact proper
mediated R2 dimension `n`.
-/
theorem exactProperMediatedR2Dimension_n_ZFC_finite
    {n : Nat} (h : 1 < n) :
    ExactProperMediatedR2Dimension
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite n :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_finite h)

/--
End-to-end finite ZFC package: nonempty residual, mediated closure,
irreducibility, and exclusion of every smaller proper mediated dimension.
-/
theorem endToEnd_ZFC_finite
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
        (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
        I_ZFC_finite
      ∧ MediatedResidualEmpty
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite (M_ZFC_finite (n := n))
      ∧ IrreducibleMediator
          (obs_ZFC_finite (n := n)) I_ZFC_finite
          (M_ZFC_finite (n := n))
      ∧ (∀ m : Nat,
          m < n →
            ¬ ExistsProperMediatedR2CertificateAtDim
              (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
              I_ZFC_finite m) :=
  endToEnd_staticProperMediatedR2Certificate
    (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
    I_ZFC_finite (M_ZFC_finite (n := n))
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_finite h)

/-!
## Replacement-based finite parameter-coordinate certificate

The Separation certificate above has a Replacement analogue on actual
Replacement schema instances.  This makes the finite exact-dimension theorem
available from either standard ZFC schema family.
-/

/-- The first canonical ZFC Replacement finite component. -/
def x_ZFC_replacement_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n :=
  zfcFiniteReplacementParameterComponent (zfcFirstCoordinate h)

/-- The second canonical ZFC Replacement finite component. -/
def y_ZFC_replacement_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n :=
  zfcFiniteReplacementParameterComponent (zfcSecondCoordinate h)

/-- The canonical ZFC Replacement finite pair. -/
def canonicalPair_ZFC_replacement_finite {n : Nat} (h : 1 < n) :
    ZFCFiniteParameterComponent n × ZFCFiniteParameterComponent n :=
  (x_ZFC_replacement_finite h, y_ZFC_replacement_finite h)

/--
All canonical finite ZFC Replacement parameter components have the same R1
trace.  They all carry Replacement schema parameter components.
-/
theorem jointSame_zfcFiniteReplacementParameterComponents
    {n : Nat} (i j : Fin n) :
    JointSame (obs_ZFC_finite (n := n)) I_ZFC_finite
      (zfcFiniteReplacementParameterComponent i)
      (zfcFiniteReplacementParameterComponent j) := by
  intro k _hk
  cases k
  rfl

/-- The canonical Replacement pair is separated by the R2 target. -/
theorem requiredAtCanonicalPair_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    RequiredDistinction (sigma_ZFC_finite (n := n))
      (canonicalPair_ZFC_replacement_finite h).1
      (canonicalPair_ZFC_replacement_finite h).2 := by
  exact zfcFirstCoordinate_ne_secondCoordinate h

/-- The canonical Replacement pair has the same R1 observation. -/
theorem jointSameAtCanonicalPair_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    JointSame (obs_ZFC_finite (n := n)) I_ZFC_finite
      (canonicalPair_ZFC_replacement_finite h).1
      (canonicalPair_ZFC_replacement_finite h).2 := by
  exact jointSame_zfcFiniteReplacementParameterComponents
    (zfcFirstCoordinate h) (zfcSecondCoordinate h)

/-- The canonical Replacement pair is a ZFC formula-component diagonal witness. -/
theorem canonicalDiagonalWitness_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    DiagonalizationWitness
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite
      (canonicalPair_ZFC_replacement_finite h).1
      (canonicalPair_ZFC_replacement_finite h).2 :=
  ⟨requiredAtCanonicalPair_ZFC_replacement_finite h,
    jointSameAtCanonicalPair_ZFC_replacement_finite h⟩

/-- The finite ZFC Replacement formula-component residual is nonempty. -/
theorem residualNonempty_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite :=
  ⟨(canonicalPair_ZFC_replacement_finite h).1,
    (canonicalPair_ZFC_replacement_finite h).2,
    canonicalDiagonalWitness_ZFC_replacement_finite h⟩

/-- The finite ZFC Replacement mediator separates the canonical pair. -/
theorem M_ZFC_replacement_finite_separates_canonicalPair
    {n : Nat} (h : 1 < n) :
    M_ZFC_finite (canonicalPair_ZFC_replacement_finite h).1 ≠
      M_ZFC_finite (canonicalPair_ZFC_replacement_finite h).2 :=
  zfcFirstCoordinate_ne_secondCoordinate h

/-- The Replacement canonical pair is indistinguishable for every proper subfamily. -/
theorem jointSameAtCanonicalPair_ZFC_replacement_finite_of_properSubfamily
    {n : Nat} (h : 1 < n)
    (K : Subfamily ZFCFiniteInterface)
    (hProper : Subfamily.Proper K I_ZFC_finite) :
    JointSame (obs_ZFC_finite (n := n)) K
      (canonicalPair_ZFC_replacement_finite h).1
      (canonicalPair_ZFC_replacement_finite h).2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_ZFC_finite_subfamily K hProper) hj)

/-- Explicit non-descent witness for every proper active subfamily. -/
theorem witnessedIrreducibleMediator_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    WitnessedIrreducibleMediator
      (obs_ZFC_finite (n := n)) I_ZFC_finite
      (M_ZFC_finite (n := n)) := by
  intro K hProper
  exact
    ⟨(canonicalPair_ZFC_replacement_finite h).1,
      (canonicalPair_ZFC_replacement_finite h).2,
      jointSameAtCanonicalPair_ZFC_replacement_finite_of_properSubfamily
        h K hProper,
      M_ZFC_replacement_finite_separates_canonicalPair h⟩

/-- The finite ZFC Replacement mediator is irreducible. -/
theorem irreducibleMediator_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    IrreducibleMediator
      (obs_ZFC_finite (n := n)) I_ZFC_finite
      (M_ZFC_finite (n := n)) :=
  witnessedIrreducibleMediator_irreducibleMediator
    (obs_ZFC_finite (n := n)) I_ZFC_finite
    (M_ZFC_finite (n := n))
    (witnessedIrreducibleMediator_M_ZFC_replacement_finite h)

/-- The finite ZFC Replacement formula components give a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    ProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨residualNonempty_ZFC_replacement_finite h,
    mediatedResidualEmpty_M_ZFC_finite,
    irreducibleMediator_M_ZFC_replacement_finite h⟩

/-- Witnessed proper mediated R2 certificate for finite ZFC Replacement components. -/
theorem witnessedProperMediatedR2Certificate_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    WitnessedProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨residualNonempty_ZFC_replacement_finite h,
    mediatedResidualEmpty_M_ZFC_finite,
    witnessedIrreducibleMediator_M_ZFC_replacement_finite h⟩

/-- Any mediated closure for the finite ZFC Replacement family induces an injection. -/
theorem injective_of_mediatedResidualEmpty_ZFC_replacement_finite
    {n m : Nat} {M : ZFCFiniteParameterComponent n → Fin m} :
    MediatedResidualEmpty
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite M →
        Function.Injective
          (fun i : Fin n => M (zfcFiniteReplacementParameterComponent i)) := by
  intro hCloses i j hM
  by_cases hij : i = j
  · exact hij
  · have hReq :
        RequiredDistinction (sigma_ZFC_finite (n := n))
          (zfcFiniteReplacementParameterComponent i)
          (zfcFiniteReplacementParameterComponent j) := by
      intro hSigma
      exact hij hSigma
    have hResidual :
        MediatedResidual
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite M
          (zfcFiniteReplacementParameterComponent i)
          (zfcFiniteReplacementParameterComponent j) :=
      ⟨hReq, ⟨jointSame_zfcFiniteReplacementParameterComponents i j, hM⟩⟩
    exact False.elim
      (hCloses
        (zfcFiniteReplacementParameterComponent i)
        (zfcFiniteReplacementParameterComponent j)
        hResidual)

/-- No smaller proper mediated certificate can close the finite Replacement family. -/
theorem no_smaller_properMediatedR2Certificate_ZFC_replacement_finite
    {n : Nat} :
    ∀ m : Nat,
      m < n →
        ¬ ExistsProperMediatedR2CertificateAtDim
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (zfcFiniteReplacementParameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_replacement_finite hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm
      (fun i : Fin n => M (zfcFiniteReplacementParameterComponent i)))
      hInjective

/-- No smaller mediated certificate can close the finite Replacement family. -/
theorem no_smaller_mediatedR2Certificate_ZFC_replacement_finite
    {n : Nat} :
    ∀ m : Nat,
      m < n →
        ¬ ExistsMediatedR2CertificateAtDim
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (zfcFiniteReplacementParameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_replacement_finite hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm
      (fun i : Fin n => M (zfcFiniteReplacementParameterComponent i)))
      hInjective

/-- The finite ZFC Replacement mediator realizes dimension-minimal closure. -/
theorem dimensionMinimalMediatedR2Certificate_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨properMediatedR2Certificate.toMediatedR2Certificate
      (properMediatedR2Certificate_M_ZFC_replacement_finite h),
    no_smaller_mediatedR2Certificate_ZFC_replacement_finite⟩

/-- The finite ZFC Replacement mediator realizes dimension-minimal closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨properMediatedR2Certificate_M_ZFC_replacement_finite h,
    no_smaller_properMediatedR2Certificate_ZFC_replacement_finite⟩

/-- The finite ZFC Replacement mediator realizes witnessed dimension-minimal closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite (M_ZFC_finite (n := n)) :=
  ⟨witnessedProperMediatedR2Certificate_M_ZFC_replacement_finite h,
    no_smaller_properMediatedR2Certificate_ZFC_replacement_finite⟩

/--
For every `n >= 2`, the finite ZFC Replacement formula-component family has
exact mediated R2 dimension `n`.
-/
theorem exactMediatedR2Dimension_n_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    ExactMediatedR2Dimension
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite n :=
  exactMediatedR2Dimension_of_dimensionMinimalCertificate
    (dimensionMinimalMediatedR2Certificate_M_ZFC_replacement_finite h)

/--
For every `n >= 2`, the finite ZFC Replacement formula-component family has
exact proper mediated R2 dimension `n`.
-/
theorem exactProperMediatedR2Dimension_n_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    ExactProperMediatedR2Dimension
      (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
      I_ZFC_finite n :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_replacement_finite h)

/--
End-to-end finite ZFC Replacement package: nonempty residual, mediated closure,
irreducibility, and exclusion of every smaller proper mediated dimension.
-/
theorem endToEnd_ZFC_replacement_finite
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
        (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
        I_ZFC_finite
      ∧ MediatedResidualEmpty
          (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
          I_ZFC_finite (M_ZFC_finite (n := n))
      ∧ IrreducibleMediator
          (obs_ZFC_finite (n := n)) I_ZFC_finite
          (M_ZFC_finite (n := n))
      ∧ (∀ m : Nat,
          m < n →
            ¬ ExistsProperMediatedR2CertificateAtDim
              (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
              I_ZFC_finite m) :=
  endToEnd_staticProperMediatedR2Certificate
    (obs_ZFC_finite (n := n)) (sigma_ZFC_finite (n := n))
    I_ZFC_finite (M_ZFC_finite (n := n))
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_replacement_finite h)

/-!
## R1/R2 certificate over the full ZFC axiom carrier

The following state type contains every `ZFCFormulaAxiom` object through the
`axiom` constructor and, in the same carrier, finite Separation and Replacement
parameter components used to witness exact dimension `n`.
-/

/-- Family classifier of a certified ZFC formula axiom. -/
def familyOfZFCFormulaAxiom : ZFCFormulaAxiom → AxiomFamily
  | ⟨_, IsZFCFormulaAxiom.extensionality⟩ => AxiomFamily.extensionality
  | ⟨_, IsZFCFormulaAxiom.empty_set⟩ => AxiomFamily.empty_set
  | ⟨_, IsZFCFormulaAxiom.pairing⟩ => AxiomFamily.pairing
  | ⟨_, IsZFCFormulaAxiom.union⟩ => AxiomFamily.union
  | ⟨_, IsZFCFormulaAxiom.power_set⟩ => AxiomFamily.power_set
  | ⟨_, IsZFCFormulaAxiom.infinity⟩ => AxiomFamily.infinity
  | ⟨_, IsZFCFormulaAxiom.separation _ _⟩ => AxiomFamily.separation
  | ⟨_, IsZFCFormulaAxiom.replacement _ _⟩ => AxiomFamily.replacement
  | ⟨_, IsZFCFormulaAxiom.foundation⟩ => AxiomFamily.foundation
  | ⟨_, IsZFCFormulaAxiom.choice⟩ => AxiomFamily.choice

/--
Full ZFC R1/R2 state carrier.

The `axiom` constructor embeds every certified ZFC formula axiom.  The
`parameterComponent` constructor embeds the finite family of actual Separation
formula components, and `replacementParameterComponent` embeds the finite
family of actual Replacement formula components.  Full axioms do not carry an
arbitrary finite coordinate; when `n` is inhabited they use the fixed default
coordinate `0`.
-/
inductive ZFCAllAxiomFiniteState (n : Nat)
  | axiom : 0 < n → ZFCFormulaAxiom → ZFCAllAxiomFiniteState n
  | parameterComponent : Fin n → ZFCAllAxiomFiniteState n
  | replacementParameterComponent : Fin n → ZFCAllAxiomFiniteState n

/-- Formula carried by a full ZFC R1/R2 state. -/
def formulaOfZFCAllAxiomFiniteState
    {n : Nat}
    (s : ZFCAllAxiomFiniteState n) : Formula :=
  match s with
  | ZFCAllAxiomFiniteState.axiom _ a => a.formula
  | ZFCAllAxiomFiniteState.parameterComponent i =>
      (zfcParameterFormulaComponent i.val).formula
  | ZFCAllAxiomFiniteState.replacementParameterComponent i =>
      (zfcReplacementParameterFormulaComponent i.val).formula

/-- R1 trace of a full ZFC R1/R2 state. -/
def traceOfZFCAllAxiomFiniteState
    {n : Nat}
    (s : ZFCAllAxiomFiniteState n) : ZFCFiniteTrace :=
  match s with
  | ZFCAllAxiomFiniteState.axiom _ a =>
      { family := familyOfZFCFormulaAxiom a
        role := ZFCComponentRole.full_axiom }
  | ZFCAllAxiomFiniteState.parameterComponent _ =>
      { family := AxiomFamily.separation
        role := ZFCComponentRole.schema_parameter }
  | ZFCAllAxiomFiniteState.replacementParameterComponent _ =>
      { family := AxiomFamily.replacement
        role := ZFCComponentRole.schema_parameter }

/-- R1 observation on the full ZFC axiom carrier. -/
def obs_ZFC_all {n : Nat} :
    ZFCFiniteInterface → ZFCAllAxiomFiniteState n → ZFCFiniteTrace
  | ZFCFiniteInterface.componentTrace, s => traceOfZFCAllAxiomFiniteState s

/-- R2 target on the full ZFC axiom carrier. -/
def sigma_ZFC_all {n : Nat}
    (s : ZFCAllAxiomFiniteState n) : Fin n :=
  match s with
  | ZFCAllAxiomFiniteState.axiom h _ => ⟨0, h⟩
  | ZFCAllAxiomFiniteState.parameterComponent i => i
  | ZFCAllAxiomFiniteState.replacementParameterComponent i => i

/-- Mediator on the full ZFC axiom carrier. -/
def M_ZFC_all {n : Nat}
    (s : ZFCAllAxiomFiniteState n) : Fin n :=
  sigma_ZFC_all s

/-- Full-carrier canonical first state. -/
def x_ZFC_all {n : Nat} (h : 1 < n) :
    ZFCAllAxiomFiniteState n :=
  ZFCAllAxiomFiniteState.parameterComponent (zfcFirstCoordinate h)

/-- Full-carrier canonical second state. -/
def y_ZFC_all {n : Nat} (h : 1 < n) :
    ZFCAllAxiomFiniteState n :=
  ZFCAllAxiomFiniteState.parameterComponent (zfcSecondCoordinate h)

/-- Full-carrier canonical pair. -/
def canonicalPair_ZFC_all {n : Nat} (h : 1 < n) :
    ZFCAllAxiomFiniteState n × ZFCAllAxiomFiniteState n :=
  (x_ZFC_all h, y_ZFC_all h)

/-- Canonical finite parameter states have the same R1 trace in the full carrier. -/
theorem jointSame_zfcAllParameterComponents
    {n : Nat} (i j : Fin n) :
    JointSame (obs_ZFC_all (n := n)) I_ZFC_finite
      (ZFCAllAxiomFiniteState.parameterComponent i)
      (ZFCAllAxiomFiniteState.parameterComponent j) := by
  intro k _hk
  cases k
  rfl

/-- The full-carrier canonical pair is separated by the R2 target. -/
theorem requiredAtCanonicalPair_ZFC_all
    {n : Nat} (h : 1 < n) :
    RequiredDistinction (sigma_ZFC_all (n := n))
      (canonicalPair_ZFC_all h).1
      (canonicalPair_ZFC_all h).2 := by
  change zfcFirstCoordinate h ≠ zfcSecondCoordinate h
  exact zfcFirstCoordinate_ne_secondCoordinate h

/-- The full-carrier canonical pair has the same R1 observation. -/
theorem jointSameAtCanonicalPair_ZFC_all
    {n : Nat} (h : 1 < n) :
    JointSame (obs_ZFC_all (n := n)) I_ZFC_finite
      (canonicalPair_ZFC_all h).1
      (canonicalPair_ZFC_all h).2 := by
  exact jointSame_zfcAllParameterComponents
    (zfcFirstCoordinate h) (zfcSecondCoordinate h)

/-- The full-carrier canonical pair is a ZFC diagonal witness. -/
theorem canonicalDiagonalWitness_ZFC_all
    {n : Nat} (h : 1 < n) :
    DiagonalizationWitness
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite
      (canonicalPair_ZFC_all h).1
      (canonicalPair_ZFC_all h).2 :=
  ⟨requiredAtCanonicalPair_ZFC_all h,
    jointSameAtCanonicalPair_ZFC_all h⟩

/-- The full ZFC carrier has a nonempty R2 residual. -/
theorem residualNonempty_ZFC_all
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite :=
  ⟨(canonicalPair_ZFC_all h).1,
    (canonicalPair_ZFC_all h).2,
    canonicalDiagonalWitness_ZFC_all h⟩

/-- The full-carrier ZFC mediator closes every mediated residual. -/
theorem mediatedResidualEmpty_M_ZFC_all
    {n : Nat} :
    MediatedResidualEmpty
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) := by
  intro x y hResidual
  exact hResidual.1 hResidual.2.2

/-- The full-carrier mediator separates the canonical pair. -/
theorem M_ZFC_all_separates_canonicalPair
    {n : Nat} (h : 1 < n) :
    M_ZFC_all (n := n) (canonicalPair_ZFC_all h).1 ≠
      M_ZFC_all (n := n) (canonicalPair_ZFC_all h).2 :=
by
  change zfcFirstCoordinate h ≠ zfcSecondCoordinate h
  exact zfcFirstCoordinate_ne_secondCoordinate h

/-- The full-carrier canonical pair is indistinguishable for every proper subfamily. -/
theorem jointSameAtCanonicalPair_ZFC_all_of_properSubfamily
    {n : Nat} (h : 1 < n)
    (K : Subfamily ZFCFiniteInterface)
    (hProper : Subfamily.Proper K I_ZFC_finite) :
    JointSame (obs_ZFC_all (n := n)) K
      (canonicalPair_ZFC_all h).1
      (canonicalPair_ZFC_all h).2 := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_ZFC_finite_subfamily K hProper) hj)

/-- Explicit non-descent witness for every proper subfamily in the full carrier. -/
theorem witnessedIrreducibleMediator_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    WitnessedIrreducibleMediator
      (obs_ZFC_all (n := n)) I_ZFC_finite
      (M_ZFC_all (n := n)) := by
  intro K hProper
  exact
    ⟨(canonicalPair_ZFC_all h).1,
      (canonicalPair_ZFC_all h).2,
      jointSameAtCanonicalPair_ZFC_all_of_properSubfamily h K hProper,
      M_ZFC_all_separates_canonicalPair h⟩

/-- The full-carrier ZFC mediator is irreducible. -/
theorem irreducibleMediator_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    IrreducibleMediator
      (obs_ZFC_all (n := n)) I_ZFC_finite
      (M_ZFC_all (n := n)) :=
  witnessedIrreducibleMediator_irreducibleMediator
    (obs_ZFC_all (n := n)) I_ZFC_finite
    (M_ZFC_all (n := n))
    (witnessedIrreducibleMediator_M_ZFC_all h)

/-- The full ZFC carrier gives a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    ProperMediatedR2Certificate
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) :=
  ⟨residualNonempty_ZFC_all h,
    mediatedResidualEmpty_M_ZFC_all,
    irreducibleMediator_M_ZFC_all h⟩

/-- Witnessed proper mediated R2 certificate for the full ZFC carrier. -/
theorem witnessedProperMediatedR2Certificate_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    WitnessedProperMediatedR2Certificate
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) :=
  ⟨residualNonempty_ZFC_all h,
    mediatedResidualEmpty_M_ZFC_all,
    witnessedIrreducibleMediator_M_ZFC_all h⟩

/-- Any mediated closure on the full carrier induces an injection `Fin n -> Fin m`. -/
theorem injective_of_mediatedResidualEmpty_ZFC_all
    {n m : Nat}
    {M : ZFCAllAxiomFiniteState n → Fin m} :
    MediatedResidualEmpty
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite M →
        Function.Injective
          (fun i : Fin n => M (ZFCAllAxiomFiniteState.parameterComponent i)) := by
  intro hCloses i j hM
  by_cases hij : i = j
  · exact hij
  · have hReq :
        RequiredDistinction (sigma_ZFC_all (n := n))
          (ZFCAllAxiomFiniteState.parameterComponent i)
          (ZFCAllAxiomFiniteState.parameterComponent j) := by
      intro hSigma
      change i = j at hSigma
      exact hij hSigma
    have hResidual :
        MediatedResidual
          (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
          I_ZFC_finite M
          (ZFCAllAxiomFiniteState.parameterComponent i)
          (ZFCAllAxiomFiniteState.parameterComponent j) :=
      ⟨hReq, ⟨jointSame_zfcAllParameterComponents i j, hM⟩⟩
    exact False.elim
      (hCloses
        (ZFCAllAxiomFiniteState.parameterComponent i)
        (ZFCAllAxiomFiniteState.parameterComponent j)
        hResidual)

/-- No smaller proper mediated certificate can close the full ZFC carrier. -/
theorem no_smaller_properMediatedR2Certificate_ZFC_all
    {n : Nat} (_h : 1 < n) :
    ∀ m : Nat,
      m < n →
        ¬ ExistsProperMediatedR2CertificateAtDim
          (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (ZFCAllAxiomFiniteState.parameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_all hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm
      (fun i : Fin n => M (ZFCAllAxiomFiniteState.parameterComponent i)))
      hInjective

/-- No smaller mediated certificate can close the full ZFC carrier. -/
theorem no_smaller_mediatedR2Certificate_ZFC_all
    {n : Nat} (_h : 1 < n) :
    ∀ m : Nat,
      m < n →
        ¬ ExistsMediatedR2CertificateAtDim
          (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
          I_ZFC_finite m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective :
      Function.Injective
        (fun i : Fin n => M (ZFCAllAxiomFiniteState.parameterComponent i)) :=
    injective_of_mediatedResidualEmpty_ZFC_all hCert.closes
  exact
    (FiniteDimensionHierarchy.no_injective_fin_of_lt
      n m hm
      (fun i : Fin n => M (ZFCAllAxiomFiniteState.parameterComponent i)))
      hInjective

/-- The full ZFC carrier realizes dimension-minimal R2 closure. -/
theorem dimensionMinimalMediatedR2Certificate_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    DimensionMinimalMediatedR2Certificate
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) :=
  ⟨properMediatedR2Certificate.toMediatedR2Certificate
      (properMediatedR2Certificate_M_ZFC_all h),
    no_smaller_mediatedR2Certificate_ZFC_all h⟩

/-- The full ZFC carrier realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    DimensionMinimalProperMediatedR2Certificate
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) :=
  ⟨properMediatedR2Certificate_M_ZFC_all h,
    no_smaller_properMediatedR2Certificate_ZFC_all h⟩

/-- The full ZFC carrier realizes witnessed dimension-minimal closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_all
    {n : Nat} (h : 1 < n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite (M_ZFC_all (n := n)) :=
  ⟨witnessedProperMediatedR2Certificate_M_ZFC_all h,
    no_smaller_properMediatedR2Certificate_ZFC_all h⟩

/--
For every `n >= 2`, the full ZFC axiom carrier with finite Separation and
Replacement parameter components has exact mediated R2 dimension `n`.
-/
theorem exactMediatedR2Dimension_n_ZFC_all
    {n : Nat} (h : 1 < n) :
    ExactMediatedR2Dimension
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite n :=
  exactMediatedR2Dimension_of_dimensionMinimalCertificate
    (dimensionMinimalMediatedR2Certificate_M_ZFC_all h)

/--
For every `n >= 2`, the full ZFC axiom carrier with finite Separation and
Replacement parameter components has exact proper mediated R2 dimension `n`.
-/
theorem exactProperMediatedR2Dimension_n_ZFC_all
    {n : Nat} (h : 1 < n) :
    ExactProperMediatedR2Dimension
      (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
      I_ZFC_finite n :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_all h)

/--
End-to-end full ZFC package: nonempty residual, mediated closure,
irreducibility, and exclusion of every smaller proper mediated dimension.
-/
theorem endToEnd_ZFC_all
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2
        (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
        I_ZFC_finite
      ∧ MediatedResidualEmpty
          (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
          I_ZFC_finite (M_ZFC_all (n := n))
      ∧ IrreducibleMediator
          (obs_ZFC_all (n := n)) I_ZFC_finite
          (M_ZFC_all (n := n))
      ∧ (∀ m : Nat,
          m < n →
            ¬ ExistsProperMediatedR2CertificateAtDim
              (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
              I_ZFC_finite m) :=
  endToEnd_staticProperMediatedR2Certificate
    (obs_ZFC_all (n := n)) (sigma_ZFC_all (n := n))
    I_ZFC_finite (M_ZFC_all (n := n))
    (dimensionMinimalProperMediatedR2Certificate_M_ZFC_all h)

end ZFCFormulaAxioms
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.Term
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.Formula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.Term.FreeIn
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.Formula.FreeIn
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.SeparationSideConditions
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.SeparationData
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ReplacementSideConditions
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ReplacementData
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcExtensionalityFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcEmptySetFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcPairingFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcUnionFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcPowerSetFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcInfinityFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcSeparationFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcReplacementFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcFoundationFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcChoiceFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcExtensionalityAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcEmptySetAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcPairingAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcUnionAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcPowerSetAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcInfinityAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcSeparationAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcReplacementAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcFoundationAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcChoiceAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.IsZFCFormulaAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ZFCFormulaAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ZFCFormulaComponent
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcParameterPhi
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcParameterSeparationFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcReplacementParameterPhi
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcParameterReplacementFormula
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.zfcParameterReplacementAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ZFCFiniteParameterComponent
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.obs_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.sigma_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.canonicalDiagonalWitness_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.properMediatedR2Certificate_M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.witnessedProperMediatedR2Certificate_M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_mediatedR2Certificate_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_properMediatedR2Certificate_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalMediatedR2Certificate_M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalProperMediatedR2Certificate_M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactMediatedR2Dimension_n_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactProperMediatedR2Dimension_n_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.endToEnd_ZFC_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.canonicalDiagonalWitness_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.properMediatedR2Certificate_M_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.witnessedProperMediatedR2Certificate_M_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_mediatedR2Certificate_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_properMediatedR2Certificate_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalMediatedR2Certificate_M_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalProperMediatedR2Certificate_M_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactMediatedR2Dimension_n_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactProperMediatedR2Dimension_n_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.endToEnd_ZFC_replacement_finite
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.familyOfZFCFormulaAxiom
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.ZFCAllAxiomFiniteState
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.formulaOfZFCAllAxiomFiniteState
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.obs_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.sigma_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.canonicalDiagonalWitness_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.properMediatedR2Certificate_M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.witnessedProperMediatedR2Certificate_M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_mediatedR2Certificate_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.no_smaller_properMediatedR2Certificate_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalMediatedR2Certificate_M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalProperMediatedR2Certificate_M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.dimensionMinimalWitnessedProperMediatedR2Certificate_M_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactMediatedR2Dimension_n_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.exactProperMediatedR2Dimension_n_ZFC_all
#print axioms LocalSemanticClosure.ZFCFormulaAxioms.endToEnd_ZFC_all
/- AXIOM_AUDIT_END -/
