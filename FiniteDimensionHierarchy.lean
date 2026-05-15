import RegimesSelfContained

/-!
# Exact mediated R2 dimensions in every finite dimension

This file proves that the R1/R2 framework is not limited to the binary
`base/step` case.

For every finite dimension `n` with `1 < n`, it constructs a self-contained
R1/R2 instance whose exact proper mediated R2 dimension is exactly `n`.

The construction is intentionally minimal:

* states are `Fin n`;
* the R1 observation regime sees only one trivial trace, so all states are
  observationally identical;
* the R2 target is the state itself, so every pair of distinct states is a
  required distinction;
* the mediator `M : Fin n -> Fin n` is the identity.

The nontrivial part is the lower bound: every proper mediated certificate of
dimension `m < n` would induce an injection `Fin n -> Fin m`, which is
constructively impossible.

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace FiniteDimensionHierarchy

open Standalone.RegimesSelfContained

/-- Remove one forbidden point from a nontrivial finite codomain. -/
def removeFinSucc {m : Nat} (a b : Fin (m + 2)) (h : b ≠ a) : Fin (m + 1) :=
  if hlt : b.val < a.val then
    ⟨b.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ a.is_lt)⟩
  else
    ⟨b.val - 1, by
      have hneVal : b.val ≠ a.val := by
        intro hv
        exact h (Fin.ext hv)
      have hgt : a.val < b.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt)
          (fun hEq => hneVal hEq.symm)
      have hbPos : 0 < b.val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt
      exact Nat.sub_one_lt_of_le hbPos (Nat.le_of_lt_succ b.is_lt)⟩

/-- Removing a fixed forbidden point is injective on the remaining points. -/
theorem removeFinSucc_injective
    {m : Nat} (a : Fin (m + 2)) {b c : Fin (m + 2)}
    (hb : b ≠ a) (hc : c ≠ a) :
    removeFinSucc a b hb = removeFinSucc a c hc → b = c := by
  by_cases hbLt : b.val < a.val
  · by_cases hcLt : c.val < a.val
    · unfold removeFinSucc
      rw [dif_pos hbLt, dif_pos hcLt]
      intro hEq
      apply Fin.ext
      exact congrArg (fun x : Fin (m + 1) => x.val) hEq
    · unfold removeFinSucc
      rw [dif_pos hbLt, dif_neg hcLt]
      intro hEq
      have hVal : b.val = c.val - 1 :=
        congrArg (fun x : Fin (m + 1) => x.val) hEq
      have hneValC : c.val ≠ a.val := by
        intro hv
        exact hc (Fin.ext hv)
      have hgtC : a.val < c.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hcLt)
          (fun hEq => hneValC hEq.symm)
      have ha_le_pred_c : a.val ≤ c.val - 1 :=
        Nat.le_sub_one_of_lt hgtC
      have ha_le_b : a.val ≤ b.val := by
        rw [hVal]
        exact ha_le_pred_c
      exact False.elim (Nat.not_lt_of_le ha_le_b hbLt)
  · by_cases hcLt : c.val < a.val
    · unfold removeFinSucc
      rw [dif_neg hbLt, dif_pos hcLt]
      intro hEq
      have hVal : b.val - 1 = c.val :=
        congrArg (fun x : Fin (m + 1) => x.val) hEq
      have hneValB : b.val ≠ a.val := by
        intro hv
        exact hb (Fin.ext hv)
      have hgtB : a.val < b.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hbLt)
          (fun hEq => hneValB hEq.symm)
      have ha_le_pred_b : a.val ≤ b.val - 1 :=
        Nat.le_sub_one_of_lt hgtB
      have ha_le_c : a.val ≤ c.val := by
        rw [← hVal]
        exact ha_le_pred_b
      exact False.elim (Nat.not_lt_of_le ha_le_c hcLt)
    · unfold removeFinSucc
      rw [dif_neg hbLt, dif_neg hcLt]
      intro hEq
      have hVal : b.val - 1 = c.val - 1 :=
        congrArg (fun x : Fin (m + 1) => x.val) hEq
      have hneValB : b.val ≠ a.val := by
        intro hv
        exact hb (Fin.ext hv)
      have hneValC : c.val ≠ a.val := by
        intro hv
        exact hc (Fin.ext hv)
      have hgtB : a.val < b.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hbLt)
          (fun hEq => hneValB hEq.symm)
      have hgtC : a.val < c.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hcLt)
          (fun hEq => hneValC hEq.symm)
      have hbPos : 0 < b.val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgtB
      have hcPos : 0 < c.val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgtC
      apply Fin.ext
      exact Nat.pred_inj hbPos hcPos hVal

/-- There is no injection from `Fin n` into a strictly smaller `Fin m`. -/
theorem no_injective_fin_of_lt
    (n m : Nat) (h : m < n) (f : Fin n → Fin m) :
    ¬ Function.Injective f := by
  induction n generalizing m with
  | zero =>
      exact False.elim (Nat.not_lt_zero m h)
  | succ n ih =>
      cases m with
      | zero =>
          intro _hf
          exact Fin.elim0 (f ⟨0, h⟩)
      | succ m =>
          cases m with
          | zero =>
              intro hf
              have hnPos : 0 < n := Nat.lt_of_succ_lt_succ h
              let x : Fin (n + 1) := Fin.castSucc ⟨0, hnPos⟩
              let y : Fin (n + 1) := Fin.last n
              have hF : f x = f y := fin_one_eq (f x) (f y)
              have hxy : x = y := hf hF
              have hVal : (0 : Nat) = n := congrArg Fin.val hxy
              have hnZero : n = 0 := hVal.symm
              rw [hnZero] at hnPos
              exact Nat.lt_irrefl 0 hnPos
          | succ m =>
              intro hf
              have hm_lt_n : m + 1 < n := Nat.lt_of_succ_lt_succ h
              let a : Fin (m + 2) := f (Fin.last n)
              let g : Fin n → Fin (m + 1) := fun i =>
                removeFinSucc a (f (Fin.castSucc i)) (by
                  intro heq
                  have hDom : Fin.castSucc i = Fin.last n := hf heq
                  have hVal : i.val = n := congrArg Fin.val hDom
                  have hiLt : i.val < n := i.is_lt
                  rw [hVal] at hiLt
                  exact Nat.lt_irrefl n hiLt)
              have hg : Function.Injective g := by
                intro i j hij
                have hF : f (Fin.castSucc i) = f (Fin.castSucc j) := by
                  exact removeFinSucc_injective a
                    (b := f (Fin.castSucc i))
                    (c := f (Fin.castSucc j))
                    (by
                      intro heq
                      have hDom : Fin.castSucc i = Fin.last n := hf heq
                      have hVal : i.val = n := congrArg Fin.val hDom
                      have hiLt : i.val < n := i.is_lt
                      rw [hVal] at hiLt
                      exact Nat.lt_irrefl n hiLt)
                    (by
                      intro heq
                      have hDom : Fin.castSucc j = Fin.last n := hf heq
                      have hVal : j.val = n := congrArg Fin.val hDom
                      have hjLt : j.val < n := j.is_lt
                      rw [hVal] at hjLt
                      exact Nat.lt_irrefl n hjLt)
                    hij
                have hCast : Fin.castSucc i = Fin.castSucc j := hf hF
                have hVal :
                    (Fin.castSucc i).val = (Fin.castSucc j).val :=
                  congrArg (fun x : Fin (n + 1) => x.val) hCast
                apply Fin.ext
                exact hVal
              exact ih (m + 1) hm_lt_n g hg

/-- The single interface used by the dimension-`n` family. -/
inductive DimensionInterface
  | trace
deriving DecidableEq

/-- The active R1 family contains only the trivial trace reader. -/
def I_dimension : Subfamily DimensionInterface
  | DimensionInterface.trace => True

/-- The R1 observation map forgets the state completely. -/
def obs_dimension {n : Nat} : DimensionInterface → Fin n → Unit
  | DimensionInterface.trace, _ => ()

/-- The R2 target is the state itself. -/
def sigma_dimension {n : Nat} (x : Fin n) : Fin n :=
  x

/-- The dimension-`n` mediator is the identity finite coordinate. -/
def M_dimension {n : Nat} (x : Fin n) : Fin n :=
  x

/-- All states are R1-identical for the trivial trace observation. -/
theorem jointSame_dimension
    {n : Nat} (x y : Fin n) :
    JointSame obs_dimension I_dimension x y := by
  intro j _hj
  cases j
  rfl

/-- The canonical first state, available when `1 < n`. -/
def firstState {n : Nat} (h : 1 < n) : Fin n :=
  ⟨0, Nat.lt_trans Nat.zero_lt_one h⟩

/-- The canonical second state, available when `1 < n`. -/
def secondState {n : Nat} (h : 1 < n) : Fin n :=
  ⟨1, h⟩

/-- The two canonical states are distinct. -/
theorem firstState_ne_secondState
    {n : Nat} (h : 1 < n) :
    firstState h ≠ secondState h := by
  intro hEq
  have hVal : (0 : Nat) = 1 := congrArg Fin.val hEq
  cases hVal

/-- The canonical pair is a dimension-`n` diagonalization witness. -/
theorem canonicalDiagonalWitness_dimension
    {n : Nat} (h : 1 < n) :
    DiagonalizationWitness obs_dimension sigma_dimension I_dimension
      (firstState h) (secondState h) := by
  exact ⟨firstState_ne_secondState h, jointSame_dimension _ _⟩

/-- The dimension-`n` residual is nonempty. -/
theorem residualNonempty_dimension
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2 (obs_dimension (n := n)) (sigma_dimension (n := n)) I_dimension := by
  exact ⟨firstState h, secondState h, canonicalDiagonalWitness_dimension h⟩

/-- The identity mediator closes every residual. -/
theorem mediatedResidualEmpty_M_dimension
    {n : Nat} :
    MediatedResidualEmpty obs_dimension sigma_dimension
      I_dimension (M_dimension (n := n)) := by
  intro x y hResidual
  exact hResidual.1 hResidual.2.2

/-- A proper subfamily omits the single trace interface. -/
theorem not_mem_of_proper_dimension_subfamily
    (K : Subfamily DimensionInterface) :
    Subfamily.Proper K I_dimension →
      ¬ K DimensionInterface.trace := by
  intro hProper
  rcases hProper with ⟨_hSubset, hMissing⟩
  rcases hMissing with ⟨j, _hjI, hjNotK⟩
  cases j
  exact hjNotK

/-- Every proper active subfamily leaves the canonical pair indistinguishable. -/
theorem jointSame_dimension_of_proper
    {n : Nat} {K : Subfamily DimensionInterface}
    (hProper : Subfamily.Proper K I_dimension)
    (x y : Fin n) :
    JointSame obs_dimension K x y := by
  intro j hj
  cases j
  exact False.elim
    ((not_mem_of_proper_dimension_subfamily K hProper) hj)

/-- The identity mediator is irreducible for the dimension-`n` family. -/
theorem irreducibleMediator_M_dimension
    {n : Nat} (h : 1 < n) :
    IrreducibleMediator obs_dimension I_dimension
      (M_dimension (n := n)) := by
  intro K hProper hDescends
  have hSame :
      JointSame obs_dimension K (firstState h) (secondState h) :=
    jointSame_dimension_of_proper hProper _ _
  exact firstState_ne_secondState h
    (hDescends (firstState h) (secondState h) hSame)

/-- The identity mediator has explicit non-descent witnesses for every proper subfamily. -/
theorem witnessedIrreducibleMediator_M_dimension
    {n : Nat} (h : 1 < n) :
    WitnessedIrreducibleMediator obs_dimension I_dimension
      (M_dimension (n := n)) := by
  intro K hProper
  exact
    ⟨firstState h,
      secondState h,
      jointSame_dimension_of_proper hProper _ _,
      firstState_ne_secondState h⟩

/-- The dimension-`n` family gives a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M_dimension
    {n : Nat} (h : 1 < n) :
    ProperMediatedR2Certificate obs_dimension sigma_dimension
      I_dimension (M_dimension (n := n)) := by
  exact
    ⟨residualNonempty_dimension h,
      mediatedResidualEmpty_M_dimension,
      irreducibleMediator_M_dimension h⟩

/-- The witnessed dimension-`n` certificate. -/
theorem witnessedProperMediatedR2Certificate_M_dimension
    {n : Nat} (h : 1 < n) :
    WitnessedProperMediatedR2Certificate obs_dimension sigma_dimension
      I_dimension (M_dimension (n := n)) := by
  exact
    ⟨residualNonempty_dimension h,
      mediatedResidualEmpty_M_dimension,
      witnessedIrreducibleMediator_M_dimension h⟩

/--
Any mediated closure certificate for the dimension-`n` family induces an
injection into the mediator codomain.
-/
theorem injective_of_mediatedResidualEmpty_dimension
    {n m : Nat} {M : Fin n → Fin m} :
    MediatedResidualEmpty obs_dimension sigma_dimension I_dimension M →
      Function.Injective M := by
  intro hCloses x y hM
  by_cases hxy : x = y
  · exact hxy
  · have hReq : RequiredDistinction sigma_dimension x y := by
      intro hSigma
      exact hxy hSigma
    have hResidual :
        MediatedResidual obs_dimension sigma_dimension I_dimension M x y :=
      ⟨hReq, ⟨jointSame_dimension x y, hM⟩⟩
    exact False.elim (hCloses x y hResidual)

/-- No smaller proper mediated certificate can close the dimension-`n` family. -/
theorem no_smaller_properMediatedR2Certificate_dimension
    {n : Nat} :
    ∀ m : Nat,
      m < n →
        ¬ ExistsProperMediatedR2CertificateAtDim
          (obs_dimension (n := n)) (sigma_dimension (n := n)) I_dimension m := by
  intro m hm hExists
  rcases hExists with ⟨M, hCert⟩
  have hInjective : Function.Injective M :=
    injective_of_mediatedResidualEmpty_dimension hCert.closes
  exact (no_injective_fin_of_lt n m hm M) hInjective

/-- The identity mediator realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M_dimension
    {n : Nat} (h : 1 < n) :
    DimensionMinimalProperMediatedR2Certificate
      obs_dimension sigma_dimension I_dimension
      (M_dimension (n := n)) := by
  exact
    ⟨properMediatedR2Certificate_M_dimension h,
      no_smaller_properMediatedR2Certificate_dimension⟩

/-- The identity mediator realizes dimension-minimal witnessed proper R2 closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M_dimension
    {n : Nat} (h : 1 < n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      obs_dimension sigma_dimension I_dimension
      (M_dimension (n := n)) := by
  exact
    ⟨witnessedProperMediatedR2Certificate_M_dimension h,
      no_smaller_properMediatedR2Certificate_dimension⟩

/-- For every `n >= 2`, the constructed family has exact proper dimension `n`. -/
theorem exactProperMediatedR2Dimension_n
    {n : Nat} (h : 1 < n) :
    ExactProperMediatedR2Dimension
      (obs_dimension (n := n)) (sigma_dimension (n := n)) I_dimension n :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M_dimension h)

/--
End-to-end dimension-`n` package: nonempty residual, mediated closure,
irreducibility, and exclusion of every smaller proper mediated dimension.
-/
theorem endToEnd_dimension_n
    {n : Nat} (h : 1 < n) :
    ResidualNonempty_R2 (obs_dimension (n := n)) (sigma_dimension (n := n)) I_dimension
      ∧ MediatedResidualEmpty obs_dimension sigma_dimension
          I_dimension (M_dimension (n := n))
      ∧ IrreducibleMediator obs_dimension I_dimension
          (M_dimension (n := n))
      ∧ (∀ m : Nat,
          m < n →
            ¬ ExistsProperMediatedR2CertificateAtDim
              (obs_dimension (n := n)) (sigma_dimension (n := n)) I_dimension m) := by
  exact
    endToEnd_staticProperMediatedR2Certificate
      obs_dimension sigma_dimension I_dimension
      (M_dimension (n := n))
      (dimensionMinimalProperMediatedR2Certificate_M_dimension h)

end FiniteDimensionHierarchy
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.removeFinSucc
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.removeFinSucc_injective
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.no_injective_fin_of_lt
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.DimensionInterface
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.obs_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.sigma_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.M_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.canonicalDiagonalWitness_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.properMediatedR2Certificate_M_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.witnessedProperMediatedR2Certificate_M_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.no_smaller_properMediatedR2Certificate_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.dimensionMinimalProperMediatedR2Certificate_M_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.dimensionMinimalWitnessedProperMediatedR2Certificate_M_dimension
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.exactProperMediatedR2Dimension_n
#print axioms LocalSemanticClosure.FiniteDimensionHierarchy.endToEnd_dimension_n
/- AXIOM_AUDIT_END -/
