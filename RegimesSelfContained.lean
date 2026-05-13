/-!
# Self-contained R1/R2 regimes

This file is a standalone version of the R1/R2 synthesis layer.

It intentionally has no imports.  It does not reuse the modular kernel.  The
goal is to expose the same conceptual architecture from first principles:

* R1 as coherence of an explicit presentation;
* R2 direct closure as absence of diagonal witnesses;
* R2 mediated closure as separation of every remaining diagonal witness by a
  finite irreducible mediator;
* incidence closure as emptiness of a common residual.

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace Standalone
namespace RegimesSelfContained

universe u v w z a

/--
Constructive membership in an explicit list.

This file does not use `List.Mem`; the witness is deliberately first-order and
auditable.
-/
inductive InList {A : Type a} (a : A) : List A → Prop
  | head {xs : List A} : InList a (a :: xs)
  | tail {b : A} {xs : List A} : InList a xs → InList a (b :: xs)

/-- Boolean count over an explicit list. -/
def countListBool {A : Type a} : List A → (A → Bool) → Nat
  | [], _b => 0
  | a :: xs, b =>
      match b a with
      | true => Nat.succ (countListBool xs b)
      | false => countListBool xs b

/-- A boolean predicate is false on every listed element. -/
inductive AllFalseBool {A : Type a} (b : A → Bool) : List A → Prop
  | nil : AllFalseBool b []
  | cons {a : A} {xs : List A} :
      b a = false → AllFalseBool b xs → AllFalseBool b (a :: xs)

/-- A zero boolean count follows from pointwise falsity on the explicit list. -/
theorem countListBool_eq_zero_of_allFalseBool
    {A : Type a} (xs : List A) (b : A → Bool) :
    AllFalseBool b xs → countListBool xs b = 0 := by
  intro h
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases h with
      | cons hHead hTail =>
          unfold countListBool
          rw [hHead]
          exact ih hTail

/-- A listed true value gives a positive boolean count. -/
theorem countListBool_pos_of_inList_true
    {A : Type a} (xs : List A) (b : A → Bool) (a : A) :
    InList a xs → b a = true → 0 < countListBool xs b := by
  induction xs with
  | nil =>
      intro hIn _hTrue
      cases hIn
  | cons c xs ih =>
      intro hIn hTrue
      cases hIn with
      | head =>
          unfold countListBool
          cases hba : b a with
          | false =>
              have hContr : false = true := hba.symm.trans hTrue
              cases hContr
          | true =>
              exact Nat.succ_pos _
      | tail hTail =>
          have hPos : 0 < countListBool xs b := ih hTail hTrue
          unfold countListBool
          cases b c with
          | false =>
              exact hPos
          | true =>
              exact Nat.succ_pos _

/-- A positive boolean count exposes a listed true witness. -/
theorem exists_inList_true_of_countListBool_pos
    {A : Type a} (xs : List A) (b : A → Bool) :
    0 < countListBool xs b → ∃ a : A, InList a xs ∧ b a = true := by
  induction xs with
  | nil =>
      intro h
      unfold countListBool at h
      exact False.elim (Nat.not_lt_zero 0 h)
  | cons x xs ih =>
      intro h
      unfold countListBool at h
      cases hb : b x with
      | false =>
          rw [hb] at h
          rcases ih h with ⟨a, hIn, hTrue⟩
          exact ⟨a, InList.tail hIn, hTrue⟩
      | true =>
          exact ⟨x, InList.head, hb⟩

def inList_append_left
    {A : Type a} {a : A} {xs ys : List A} :
    InList a xs → InList a (xs ++ ys)
  | InList.head => InList.head
  | InList.tail hTail => InList.tail (inList_append_left hTail)

def inList_append_right
    {A : Type a} {a : A} (xs : List A) {ys : List A} :
    InList a ys → InList a (xs ++ ys) :=
  match xs with
  | [] => fun h => h
  | _ :: xs => fun h => InList.tail (inList_append_right xs h)

/-- A family of interfaces, represented constructively as a predicate. -/
abbrev Subfamily (J : Type u) : Type u :=
  J → Prop

namespace Subfamily

/-- Inclusion of interface families. -/
def Subset {J : Type u} (K I : Subfamily J) : Prop :=
  ∀ j : J, K j → I j

/-- Proper inclusion of interface families. -/
def Proper {J : Type u} (K I : Subfamily J) : Prop :=
  Subset K I ∧ ∃ j : J, I j ∧ ¬ K j

end Subfamily

/--
Abstract explicit-presentation regime.

This records only the certificate shape used by R1: an internal obstruction
to the explicit presentation.
-/
structure ExplicitPresentationRegime where
  obstruction : Prop

/-- R1 coherence: no internal obstruction is realized. -/
def Coherent_R1 (R : ExplicitPresentationRegime) : Prop :=
  ¬ R.obstruction

/-- Two states are jointly indistinguishable by every interface in `I`. -/
def JointSame {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J) (x y : S) : Prop :=
  ∀ j : J, I j → obs j x = obs j y

/-- The target signature requires `x` and `y` to remain distinct. -/
def RequiredDistinction {S : Type v} {Y : Type z}
    (sigma : S → Y) (x y : S) : Prop :=
  sigma x ≠ sigma y

/-- Boolean equality from decidable equality. -/
def eqBool {A : Type a} [DecidableEq A] (x y : A) : Bool :=
  match (inferInstance : Decidable (x = y)) with
  | isTrue _ => true
  | isFalse _ => false

/-- Boolean inequality from decidable equality. -/
def neqBool {A : Type a} [DecidableEq A] (x y : A) : Bool :=
  match (inferInstance : Decidable (x = y)) with
  | isTrue _ => false
  | isFalse _ => true

theorem eq_of_eqBool_true
    {A : Type a} [DecidableEq A] {x y : A} :
    eqBool x y = true → x = y := by
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue hEq =>
      intro _h
      exact hEq
  | isFalse _hNe =>
      intro h
      cases h

theorem eqBool_true_of_eq
    {A : Type a} [DecidableEq A] {x y : A} :
    x = y → eqBool x y = true := by
  intro hEq
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue _h =>
      rfl
  | isFalse hNe =>
      exact False.elim (hNe hEq)

theorem requiredDistinction_of_neqBool_true
    {S : Type v} {Y : Type z} [DecidableEq Y]
    {x y : S} (sigma : S → Y) :
    neqBool (sigma x) (sigma y) = true → RequiredDistinction sigma x y := by
  unfold neqBool RequiredDistinction
  cases (inferInstance : Decidable (sigma x = sigma y)) with
  | isTrue _hEq =>
      intro h
      cases h
  | isFalse hNe =>
      intro _h
      exact hNe

theorem neqBool_true_of_requiredDistinction
    {S : Type v} {Y : Type z} [DecidableEq Y]
    {x y : S} (sigma : S → Y) :
    RequiredDistinction sigma x y → neqBool (sigma x) (sigma y) = true := by
  intro hReq
  unfold RequiredDistinction at hReq
  unfold neqBool
  cases (inferInstance : Decidable (sigma x = sigma y)) with
  | isTrue hEq =>
      exact False.elim (hReq hEq)
  | isFalse _hNe =>
      rfl

/--
A diagonal witness: the target separates `x` and `y`, while the current
interface regime does not.
-/
def DiagonalizationWitness
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J)
    (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ JointSame obs I x y

/-- In this standalone layer, the R2 residual witness is the diagonal witness. -/
abbrev Residual_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J)
    (x y : S) : Prop :=
  DiagonalizationWitness obs sigma I x y

/-- The R2 residual is empty when no diagonal witness remains. -/
def ResidualEmpty_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∀ x y : S, ¬ Residual_R2 obs sigma I x y

/-- The R2 residual is nonempty when some diagonal witness remains. -/
def ResidualNonempty_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∃ x y : S, Residual_R2 obs sigma I x y

/-- Direct R2 closure: the interface regime preserves every required distinction. -/
def Closed_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∀ x y : S, JointSame obs I x y → sigma x = sigma y

/-- Direct R2 closure is residual emptiness. -/
theorem closed_R2_iff_residualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed_R2 obs sigma I ↔ ResidualEmpty_R2 obs sigma I := by
  constructor
  · intro hClosed x y hResidual
    exact hResidual.1 (hClosed x y hResidual.2)
  · intro hEmpty x y hSame
    by_cases hEq : sigma x = sigma y
    · exact hEq
    · exact False.elim (hEmpty x y ⟨hEq, hSame⟩)

/-- Direct R2 closure is absence of diagonal witnesses. -/
theorem closed_R2_iff_no_diagonalizationWitness
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed_R2 obs sigma I ↔
      ∀ x y : S, ¬ DiagonalizationWitness obs sigma I x y :=
  closed_R2_iff_residualEmpty obs sigma I

/-- Joint indistinguishability over an explicit finite interface list. -/
def JointSameList
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) : List J → S → S → Prop
  | [], _x, _y => True
  | j :: js, x, y => obs j x = obs j y ∧ JointSameList obs js x y

/-- Listed residual over explicit finite interfaces. -/
def ResidualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ JointSameList obs interfaces x y

/-- Boolean joint indistinguishability over an explicit finite interface list. -/
def JointSameListBool
    {J : Type u} {S : Type v} {V : Type w}
    [DecidableEq V] (obs : J → S → V) : List J → S → S → Bool
  | [], _x, _y => true
  | j :: js, x, y =>
      match eqBool (obs j x) (obs j y) with
      | true => JointSameListBool obs js x y
      | false => false

/-- Boolean listed residual over explicit finite interfaces. -/
def ResidualListBool
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Bool :=
  match neqBool (sigma x) (sigma y) with
  | true => JointSameListBool obs interfaces x y
  | false => false

def pairWith {S : Type v} (x : S) : List S → List (S × S)
  | [] => []
  | y :: ys => (x, y) :: pairWith x ys

def pairLists {S : Type v} : List S → List S → List (S × S)
  | [], _ys => []
  | x :: xs, ys => pairWith x ys ++ pairLists xs ys

def inList_pairWith_of_inList
    {S : Type v} (x : S) {y : S} {ys : List S} :
    InList y ys → InList (x, y) (pairWith x ys)
  | InList.head => InList.head
  | InList.tail hTail => InList.tail (inList_pairWith_of_inList x hTail)

def inList_pairLists_of_inList
    {S : Type v} {x y : S} {rows cols : List S} :
    InList x rows → InList y cols → InList (x, y) (pairLists rows cols)
  | InList.head, hY => inList_append_left (inList_pairWith_of_inList x hY)
  | InList.tail hTail, hY => inList_append_right _ (inList_pairLists_of_inList hTail hY)

theorem jointSameList_of_bool_true
    {J : Type u} {S : Type v} {V : Type w} [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) :
    JointSameListBool obs interfaces x y = true → JointSameList obs interfaces x y := by
  induction interfaces with
  | nil =>
      intro _h
      exact True.intro
  | cons j js ih =>
      intro h
      unfold JointSameListBool at h
      cases hEq : eqBool (obs j x) (obs j y) with
      | false =>
          rw [hEq] at h
          cases h
      | true =>
          rw [hEq] at h
          exact ⟨eq_of_eqBool_true hEq, ih h⟩

theorem bool_true_of_jointSameList
    {J : Type u} {S : Type v} {V : Type w} [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) :
    JointSameList obs interfaces x y → JointSameListBool obs interfaces x y = true := by
  induction interfaces with
  | nil =>
      intro _h
      rfl
  | cons j js ih =>
      intro h
      unfold JointSameListBool
      have hEq : eqBool (obs j x) (obs j y) = true := eqBool_true_of_eq h.1
      rw [hEq]
      exact ih h.2

theorem residualList_of_bool_true
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    ResidualListBool obs sigma interfaces x y = true →
      ResidualList obs sigma interfaces x y := by
  intro h
  unfold ResidualListBool at h
  cases hReq : neqBool (sigma x) (sigma y) with
  | false =>
      rw [hReq] at h
      cases h
  | true =>
      rw [hReq] at h
      exact ⟨requiredDistinction_of_neqBool_true sigma hReq,
        jointSameList_of_bool_true obs interfaces x y h⟩

theorem bool_true_of_residualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    ResidualList obs sigma interfaces x y →
      ResidualListBool obs sigma interfaces x y = true := by
  intro h
  unfold ResidualListBool
  have hReq : neqBool (sigma x) (sigma y) = true :=
    neqBool_true_of_requiredDistinction sigma h.1
  rw [hReq]
  exact bool_true_of_jointSameList obs interfaces x y h.2

theorem jointSameList_eq_of_inList
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) {interfaces : List J} {x y : S} {j : J} :
    JointSameList obs interfaces x y → InList j interfaces → obs j x = obs j y := by
  intro hJoint hIn
  induction interfaces with
  | nil =>
      cases hIn
  | cons k ks ih =>
      cases hIn with
      | head =>
          exact hJoint.1
      | tail hTail =>
          exact ih hJoint.2 hTail

theorem jointSame_of_jointSameList
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, I j → InList j interfaces) :
    JointSameList obs interfaces x y → JointSame obs I x y := by
  intro hList j hj
  exact jointSameList_eq_of_inList obs hList (hEnum j hj)

theorem jointSameList_of_jointSame
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, InList j interfaces → I j) :
    JointSame obs I x y → JointSameList obs interfaces x y := by
  intro hJoint
  induction interfaces with
  | nil =>
      exact True.intro
  | cons j js ih =>
      refine ⟨?_, ?_⟩
      · exact hJoint j (hEnum j InList.head)
      · exact ih (fun k hk => hEnum k (InList.tail hk))

theorem residual_of_residualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, I j → InList j interfaces) :
    ResidualList obs sigma interfaces x y → Residual_R2 obs sigma I x y := by
  intro hRes
  exact ⟨hRes.1, jointSame_of_jointSameList obs hEnum hRes.2⟩

theorem residualList_of_residual
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, InList j interfaces → I j) :
    Residual_R2 obs sigma I x y → ResidualList obs sigma interfaces x y := by
  intro hRes
  exact ⟨hRes.1, jointSameList_of_jointSame obs hEnum hRes.2⟩

/-- Numerical residual size over explicit lists of states and interfaces. -/
def rho
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  countListBool (pairLists states states)
    (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)

/-- Exhaustive finite presentation of the state/interface referential. -/
structure ExhaustiveFiniteResidualPresentation
    {J : Type u} {S : Type v}
    (states : List S) (interfaces : List J) (I : Subfamily J) : Prop where
  states_exhaustive : ∀ s : S, InList s states
  interfaces_complete : ∀ j : J, I j → InList j interfaces
  interfaces_sound : ∀ j : J, InList j interfaces → I j

/-- The finite residual coordinate is the explicit counted residual. -/
def finiteResidualCoordinate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  rho states obs sigma interfaces

/-- In an exhaustive finite presentation, positive rho exposes a residual witness. -/
theorem finiteResidualCoordinate_pos_iff_residualNonempty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hPresentation :
      ExhaustiveFiniteResidualPresentation states interfaces I) :
    0 < finiteResidualCoordinate states obs sigma interfaces ↔
      ResidualNonempty_R2 obs sigma I := by
  constructor
  · intro hPos
    unfold finiteResidualCoordinate rho at hPos
    rcases exists_inList_true_of_countListBool_pos
        (pairLists states states)
        (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
        hPos with
      ⟨xy, _hIn, hTrue⟩
    exact ⟨xy.1, xy.2,
      residual_of_residualList obs sigma hPresentation.interfaces_complete
        (residualList_of_bool_true obs sigma interfaces xy.1 xy.2 hTrue)⟩
  · intro hNonempty
    rcases hNonempty with ⟨x, y, hRes⟩
    have hPair : InList (x, y) (pairLists states states) :=
      inList_pairLists_of_inList
        (hPresentation.states_exhaustive x)
        (hPresentation.states_exhaustive y)
    have hResListed : ResidualList obs sigma interfaces x y :=
      residualList_of_residual obs sigma hPresentation.interfaces_sound hRes
    have hBoolTrue :
        ResidualListBool obs sigma interfaces (x, y).1 (x, y).2 = true :=
      bool_true_of_residualList obs sigma interfaces x y hResListed
    unfold finiteResidualCoordinate rho
    exact countListBool_pos_of_inList_true
      (pairLists states states)
      (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
      (x, y) hPair hBoolTrue

/-- In an exhaustive finite presentation, zero rho is residual emptiness. -/
theorem finiteResidualCoordinate_zero_iff_residualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hPresentation :
      ExhaustiveFiniteResidualPresentation states interfaces I) :
    finiteResidualCoordinate states obs sigma interfaces = 0 ↔
      ResidualEmpty_R2 obs sigma I := by
  constructor
  · intro hZero x y hRes
    have hNonempty : ResidualNonempty_R2 obs sigma I := ⟨x, y, hRes⟩
    have hPos : 0 < finiteResidualCoordinate states obs sigma interfaces :=
      (finiteResidualCoordinate_pos_iff_residualNonempty
        states obs sigma interfaces I hPresentation).2 hNonempty
    rw [hZero] at hPos
    exact False.elim (Nat.not_lt_zero 0 hPos)
  · intro hEmpty
    by_cases hZero : finiteResidualCoordinate states obs sigma interfaces = 0
    · exact hZero
    · have hPos : 0 < finiteResidualCoordinate states obs sigma interfaces :=
        Nat.pos_of_ne_zero hZero
      have hNonempty : ResidualNonempty_R2 obs sigma I :=
        (finiteResidualCoordinate_pos_iff_residualNonempty
          states obs sigma interfaces I hPresentation).1 hPos
      rcases hNonempty with ⟨x, y, hRes⟩
      exact False.elim (hEmpty x y hRes)

/-- In an exhaustive finite presentation, zero rho is direct R2 closure. -/
theorem finiteResidualCoordinate_zero_iff_closed_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hPresentation :
      ExhaustiveFiniteResidualPresentation states interfaces I) :
    finiteResidualCoordinate states obs sigma interfaces = 0 ↔
      Closed_R2 obs sigma I :=
  (finiteResidualCoordinate_zero_iff_residualEmpty
    states obs sigma interfaces I hPresentation).trans
      (closed_R2_iff_residualEmpty obs sigma I).symm

/-- Descent of a mediator to a subfamily. -/
def MediatorDescendsSubfamily
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  ∀ x y : S, JointSame obs K x y → M x = M y

/-- Irreducibility: the mediator does not descend to any proper subfamily. -/
def IrreducibleMediator
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  ∀ K : Subfamily J,
    Subfamily.Proper K I → ¬ MediatorDescendsSubfamily obs K M

/--
Explicit witness that the mediator does not descend to `K`: two states remain
indistinguishable for `K`, while the mediator separates them.
-/
def MediatorNonDescentWitness
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  ∃ x y : S, JointSame obs K x y ∧ M x ≠ M y

/--
Witness-style irreducibility: every proper subfamily has an explicit
non-descent witness.
-/
def WitnessedIrreducibleMediator
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  ∀ K : Subfamily J,
    Subfamily.Proper K I → MediatorNonDescentWitness obs K M

/-- Witness-style irreducibility implies the negated descent formulation. -/
theorem witnessedIrreducibleMediator_irreducibleMediator
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (M : S → Fin n) :
    WitnessedIrreducibleMediator obs I M →
      IrreducibleMediator obs I M := by
  intro hWitnessed K hProper hDescends
  rcases hWitnessed K hProper with ⟨x, y, hSame, hNe⟩
  exact hNe (hDescends x y hSame)

/-- Joint indistinguishability after adding a finite mediator. -/
def MediatedSame
    {J : Type u} {S : Type v} {V : Type w} {n : Nat}
    (obs : J → S → V) (I : Subfamily J)
    (M : S → Fin n) (x y : S) : Prop :=
  JointSame obs I x y ∧ M x = M y

/-- R2 residual after adding a finite mediator. -/
def MediatedResidual
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J)
    (M : S → Fin n) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ MediatedSame obs I M x y

/-- No required distinction remains jointly lost after mediation. -/
def MediatedResidualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J)
    (M : S → Fin n) : Prop :=
  ∀ x y : S, ¬ MediatedResidual obs sigma I M x y

/-- Listed residual after adding a finite mediator. -/
def MediatedResidualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧
    JointSameList obs interfaces x y ∧
      M x = M y

/-- Boolean listed residual after adding a finite mediator. -/
def MediatedResidualListBool
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) (x y : S) : Bool :=
  match ResidualListBool obs sigma interfaces x y with
  | true => eqBool (M x) (M y)
  | false => false

theorem mediatedResidualList_of_bool_true
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) (x y : S) :
    MediatedResidualListBool obs sigma interfaces M x y = true →
      MediatedResidualList obs sigma interfaces M x y := by
  intro h
  unfold MediatedResidualListBool at h
  cases hResidual : ResidualListBool obs sigma interfaces x y with
  | false =>
      rw [hResidual] at h
      cases h
  | true =>
      rw [hResidual] at h
      have hListed : ResidualList obs sigma interfaces x y :=
        residualList_of_bool_true obs sigma interfaces x y hResidual
      exact ⟨hListed.1, hListed.2, eq_of_eqBool_true h⟩

theorem bool_true_of_mediatedResidualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) (x y : S) :
    MediatedResidualList obs sigma interfaces M x y →
      MediatedResidualListBool obs sigma interfaces M x y = true := by
  intro h
  unfold MediatedResidualListBool
  have hResidual : ResidualList obs sigma interfaces x y :=
    ⟨h.1, h.2.1⟩
  have hResidualBool :
      ResidualListBool obs sigma interfaces x y = true :=
    bool_true_of_residualList obs sigma interfaces x y hResidual
  rw [hResidualBool]
  exact eqBool_true_of_eq h.2.2

theorem mediatedResidual_of_mediatedResidualList
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {M : S → Fin n} {x y : S}
    (hEnum : ∀ j : J, I j → InList j interfaces) :
    MediatedResidualList obs sigma interfaces M x y →
      MediatedResidual obs sigma I M x y := by
  intro h
  exact ⟨h.1, ⟨jointSame_of_jointSameList obs hEnum h.2.1, h.2.2⟩⟩

theorem mediatedResidualList_of_mediatedResidual
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {M : S → Fin n} {x y : S}
    (hEnum : ∀ j : J, InList j interfaces → I j) :
    MediatedResidual obs sigma I M x y →
      MediatedResidualList obs sigma interfaces M x y := by
  intro h
  exact ⟨h.1, jointSameList_of_jointSame obs hEnum h.2.1, h.2.2⟩

/-- Numerical mediated residual size over explicit states and interfaces. -/
def mediatedRho
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) : Nat :=
  countListBool (pairLists states states)
    (fun xy : S × S =>
      MediatedResidualListBool obs sigma interfaces M xy.1 xy.2)

/-- The mediated finite coordinate is the counted residual after adding `M`. -/
def mediatedFiniteResidualCoordinate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (M : S → Fin n) : Nat :=
  mediatedRho states obs sigma interfaces M

/--
In an exhaustive finite presentation, positive mediated rho exposes a
mediated residual witness.
-/
theorem mediatedFiniteResidualCoordinate_pos_iff_mediatedResidualNonempty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J) (M : S → Fin n)
    (hPresentation :
      ExhaustiveFiniteResidualPresentation states interfaces I) :
    0 < mediatedFiniteResidualCoordinate states obs sigma interfaces M ↔
      ∃ x y : S, MediatedResidual obs sigma I M x y := by
  constructor
  · intro hPos
    unfold mediatedFiniteResidualCoordinate mediatedRho at hPos
    rcases exists_inList_true_of_countListBool_pos
        (pairLists states states)
        (fun xy : S × S =>
          MediatedResidualListBool obs sigma interfaces M xy.1 xy.2)
        hPos with
      ⟨xy, _hIn, hTrue⟩
    exact ⟨xy.1, xy.2,
      mediatedResidual_of_mediatedResidualList obs sigma
        hPresentation.interfaces_complete
        (mediatedResidualList_of_bool_true
          obs sigma interfaces M xy.1 xy.2 hTrue)⟩
  · intro hNonempty
    rcases hNonempty with ⟨x, y, hRes⟩
    have hPair : InList (x, y) (pairLists states states) :=
      inList_pairLists_of_inList
        (hPresentation.states_exhaustive x)
        (hPresentation.states_exhaustive y)
    have hListed : MediatedResidualList obs sigma interfaces M x y :=
      mediatedResidualList_of_mediatedResidual obs sigma
        hPresentation.interfaces_sound hRes
    have hBoolTrue :
        MediatedResidualListBool obs sigma interfaces M
          (x, y).1 (x, y).2 = true :=
      bool_true_of_mediatedResidualList obs sigma interfaces M x y hListed
    unfold mediatedFiniteResidualCoordinate mediatedRho
    exact countListBool_pos_of_inList_true
      (pairLists states states)
      (fun xy : S × S =>
        MediatedResidualListBool obs sigma interfaces M xy.1 xy.2)
      (x, y) hPair hBoolTrue

/--
In an exhaustive finite presentation, zero mediated rho is mediated residual
emptiness.
-/
theorem mediatedFiniteResidualCoordinate_zero_iff_mediatedResidualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J) (M : S → Fin n)
    (hPresentation :
      ExhaustiveFiniteResidualPresentation states interfaces I) :
    mediatedFiniteResidualCoordinate states obs sigma interfaces M = 0 ↔
      MediatedResidualEmpty obs sigma I M := by
  constructor
  · intro hZero x y hRes
    have hNonempty : ∃ x y : S, MediatedResidual obs sigma I M x y :=
      ⟨x, y, hRes⟩
    have hPos :
        0 < mediatedFiniteResidualCoordinate states obs sigma interfaces M :=
      (mediatedFiniteResidualCoordinate_pos_iff_mediatedResidualNonempty
        states obs sigma interfaces I M hPresentation).2 hNonempty
    rw [hZero] at hPos
    exact False.elim (Nat.not_lt_zero 0 hPos)
  · intro hEmpty
    by_cases hZero :
        mediatedFiniteResidualCoordinate states obs sigma interfaces M = 0
    · exact hZero
    · have hPos :
          0 < mediatedFiniteResidualCoordinate states obs sigma interfaces M :=
        Nat.pos_of_ne_zero hZero
      have hNonempty : ∃ x y : S, MediatedResidual obs sigma I M x y :=
        (mediatedFiniteResidualCoordinate_pos_iff_mediatedResidualNonempty
          states obs sigma interfaces I M hPresentation).1 hPos
      rcases hNonempty with ⟨x, y, hRes⟩
      exact False.elim (hEmpty x y hRes)

/-- Complete static R2 mediated certificate. -/
structure MediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  closes :
    MediatedResidualEmpty obs sigma I M
  irreducible :
    IrreducibleMediator obs I M

/-- Proper static R2 mediated certificate: residual first, mediated closure after. -/
structure ProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  residual_exists :
    ResidualNonempty_R2 obs sigma I
  closes :
    MediatedResidualEmpty obs sigma I M
  irreducible :
    IrreducibleMediator obs I M

/--
Witnessed proper R2 mediated certificate: the residual exists, the mediator
closes it, and every proper subfamily failure is witnessed by states.
-/
structure WitnessedProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  residual_exists :
    ResidualNonempty_R2 obs sigma I
  closes :
    MediatedResidualEmpty obs sigma I M
  witnessed_irreducible :
    WitnessedIrreducibleMediator obs I M

/-- A witnessed proper certificate induces the ordinary proper certificate. -/
theorem witnessedProperMediatedR2Certificate.toProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} :
    WitnessedProperMediatedR2Certificate obs sigma I M →
      ProperMediatedR2Certificate obs sigma I M := by
  intro h
  exact
    ⟨h.residual_exists,
      h.closes,
      witnessedIrreducibleMediator_irreducibleMediator obs I M
        h.witnessed_irreducible⟩

/-- A proper mediated certificate is, in particular, a mediated certificate. -/
theorem properMediatedR2Certificate.toMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} :
    ProperMediatedR2Certificate obs sigma I M →
      MediatedR2Certificate obs sigma I M := by
  intro h
  exact ⟨h.closes, h.irreducible⟩

/-- A nonempty residual rules out direct R2 closure. -/
theorem residualNonempty_not_closed_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    ResidualNonempty_R2 obs sigma I → ¬ Closed_R2 obs sigma I := by
  intro hNonempty hClosed
  rcases hNonempty with ⟨x, y, hResidual⟩
  have hEmpty : ResidualEmpty_R2 obs sigma I :=
    (closed_R2_iff_residualEmpty obs sigma I).1 hClosed
  exact hEmpty x y hResidual

/--
A proper mediated certificate proves that the original regime was not already
directly closed.
-/
theorem properMediatedR2Certificate_not_closed_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) :
    ProperMediatedR2Certificate obs sigma I M →
      ¬ Closed_R2 obs sigma I := by
  intro h
  exact residualNonempty_not_closed_R2 obs sigma I h.residual_exists

/-- There is some mediated R2 certificate at finite dimension `n`. -/
def ExistsMediatedR2CertificateAtDim
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n : Nat) : Prop :=
  ∃ M : S → Fin n, MediatedR2Certificate obs sigma I M

/-- There is some proper mediated R2 certificate at finite dimension `n`. -/
def ExistsProperMediatedR2CertificateAtDim
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n : Nat) : Prop :=
  ∃ M : S → Fin n, ProperMediatedR2Certificate obs sigma I M

/--
Exact finite mediated dimension: a mediated certificate exists at `n`, and no
mediated certificate exists at any strictly smaller dimension.
-/
structure ExactMediatedR2Dimension
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n : Nat) : Prop where
  exists_at :
    ExistsMediatedR2CertificateAtDim obs sigma I n
  no_smaller :
    ∀ m : Nat, m < n → ¬ ExistsMediatedR2CertificateAtDim obs sigma I m

/--
Exact finite proper mediated dimension: a proper mediated certificate exists at
`n`, and no proper mediated certificate exists at any strictly smaller
dimension.
-/
structure ExactProperMediatedR2Dimension
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n : Nat) : Prop where
  exists_at :
    ExistsProperMediatedR2CertificateAtDim obs sigma I n
  no_smaller :
    ∀ m : Nat, m < n → ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m

/--
A particular mediator realizes an exact finite mediated R2 dimension.
-/
structure DimensionMinimalMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  certificate :
    MediatedR2Certificate obs sigma I M
  no_smaller :
    ∀ m : Nat, m < n → ¬ ExistsMediatedR2CertificateAtDim obs sigma I m

/--
A particular mediator realizes an exact finite proper mediated R2 dimension.
-/
structure DimensionMinimalProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  certificate :
    ProperMediatedR2Certificate obs sigma I M
  no_smaller :
    ∀ m : Nat, m < n → ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m

/--
Dimension-minimal witnessed proper mediated certificate.

This is the strongest standalone static package: the residual is explicit, the
mediator closes it, every proper subfamily failure has an explicit state-level
witness, and no strictly smaller proper mediated certificate exists.
-/
structure DimensionMinimalWitnessedProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) : Prop where
  certificate :
    WitnessedProperMediatedR2Certificate obs sigma I M
  no_smaller :
    ∀ m : Nat, m < n → ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m

/--
A dimension-minimal witnessed proper certificate induces the ordinary
dimension-minimal proper certificate.
-/
theorem dimensionMinimalProper_of_witnessed
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} :
    DimensionMinimalWitnessedProperMediatedR2Certificate obs sigma I M →
      DimensionMinimalProperMediatedR2Certificate obs sigma I M := by
  intro h
  exact
    ⟨witnessedProperMediatedR2Certificate.toProperMediatedR2Certificate
        h.certificate,
      h.no_smaller⟩

/-- A dimension-minimal mediated certificate gives exact mediated dimension. -/
theorem exactMediatedR2Dimension_of_dimensionMinimalCertificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} :
    DimensionMinimalMediatedR2Certificate obs sigma I M →
      ExactMediatedR2Dimension obs sigma I n := by
  intro h
  exact ⟨⟨M, h.certificate⟩, h.no_smaller⟩

/-- A dimension-minimal proper mediated certificate gives exact proper dimension. -/
theorem exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} :
    DimensionMinimalProperMediatedR2Certificate obs sigma I M →
      ExactProperMediatedR2Dimension obs sigma I n := by
  intro h
  exact ⟨⟨M, h.certificate⟩, h.no_smaller⟩

/-- Exact mediated dimension excludes every smaller mediated certificate. -/
theorem no_smaller_mediatedR2Certificate_of_exactDimension
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n m : Nat) :
    ExactMediatedR2Dimension obs sigma I n →
      m < n → ¬ ExistsMediatedR2CertificateAtDim obs sigma I m := by
  intro hExact hm
  exact hExact.no_smaller m hm

/-- Exact proper mediated dimension excludes every smaller proper certificate. -/
theorem no_smaller_properMediatedR2Certificate_of_exactProperDimension
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n m : Nat) :
    ExactProperMediatedR2Dimension obs sigma I n →
      m < n → ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m := by
  intro hExact hm
  exact hExact.no_smaller m hm

/--
End-to-end static proper R2 certificate: residual present before mediation,
mediated residual closed by `M`, no descent to proper subfamilies, and no
strictly smaller proper mediated certificate exists.
-/
theorem endToEnd_staticProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) :
    DimensionMinimalProperMediatedR2Certificate obs sigma I M →
      ResidualNonempty_R2 obs sigma I
        ∧ MediatedResidualEmpty obs sigma I M
        ∧ IrreducibleMediator obs I M
        ∧ (∀ m : Nat,
            m < n →
              ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m) := by
  intro h
  exact
    ⟨h.certificate.residual_exists,
      h.certificate.closes,
      h.certificate.irreducible,
      h.no_smaller⟩

/--
End-to-end witnessed static proper R2 certificate.

Compared with `endToEnd_staticProperMediatedR2Certificate`, this keeps the
proper-subfamily obstruction in explicit witness form.
-/
theorem endToEnd_staticWitnessedProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate obs sigma I M →
      ResidualNonempty_R2 obs sigma I
        ∧ MediatedResidualEmpty obs sigma I M
        ∧ WitnessedIrreducibleMediator obs I M
        ∧ (∀ m : Nat,
            m < n →
              ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I m) := by
  intro h
  exact
    ⟨h.certificate.residual_exists,
      h.certificate.closes,
      h.certificate.witnessed_irreducible,
      h.no_smaller⟩

/--
The mediated residual is empty exactly when the mediator separates every
diagonal witness left open by the original interface regime.
-/
theorem mediatedResidualEmpty_iff_mediator_separates_witnesses
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J)
    (M : S → Fin n) :
    MediatedResidualEmpty obs sigma I M ↔
      ∀ x y : S,
        DiagonalizationWitness obs sigma I x y → M x ≠ M y := by
  constructor
  · intro hEmpty x y hWitness hMxy
    exact hEmpty x y ⟨hWitness.1, ⟨hWitness.2, hMxy⟩⟩
  · intro hSeparates x y hMediated
    exact hSeparates x y ⟨hMediated.1, hMediated.2.1⟩ hMediated.2.2

/-- An irreducible mediator is inaccessible to every proper subfamily. -/
theorem irreducibleMediator_nonDescends_properSubfamily
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I K : Subfamily J)
    {n : Nat} (M : S → Fin n) :
    IrreducibleMediator obs I M →
      Subfamily.Proper K I →
        ¬ MediatorDescendsSubfamily obs K M := by
  intro hIrred hProper
  exact hIrred K hProper

/-- Incidence-level common residual. -/
def CommonResidual {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) (d : D) : Prop :=
  Required d ∧ ∀ j : J, I j → Loss j d

/-- Incidence-level residual emptiness. -/
def CommonResidualEmpty {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) : Prop :=
  ∀ d : D, ¬ CommonResidual Required Loss I d

/-- Incidence-level residual non-emptiness, stated with an explicit witness. -/
def CommonResidualNonempty {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) : Prop :=
  ∃ d : D, CommonResidual Required Loss I d

/-- Closure by losses is emptiness of the incidence residual. -/
def ClosedByLoss {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) : Prop :=
  CommonResidualEmpty Required Loss I

/-- Irreducible closure by losses. -/
def IrreducibleClosedByLoss {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) : Prop :=
  ClosedByLoss Required Loss I ∧
    ∀ K : Subfamily J,
      Subfamily.Proper K I → ¬ ClosedByLoss Required Loss K

/-- Direct incidence closure is common-residual emptiness. -/
theorem closedByLoss_iff_commonResidualEmpty
    {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J) :
    ClosedByLoss Required Loss I ↔
      CommonResidualEmpty Required Loss I :=
  Iff.rfl

/-- Boolean all-loss test over a finite interface presentation. -/
def allLossBool {D : Type u} {J : Type v}
    (loss : J → D → Bool) : List J → D → Bool
  | [], _ => true
  | j :: js, d => loss j d && allLossBool loss js d

/-- Boolean residual test for incidence arithmetic. -/
def residualBool {D : Type u} {J : Type v}
    (required : D → Bool) (loss : J → D → Bool)
    (interfaces : List J) (d : D) : Bool :=
  required d && allLossBool loss interfaces d

/-- Cardinal projection of finite incidence residuals. -/
def rhoList {D : Type u} {J : Type v}
    (distinctions : List D) (required : D → Bool)
    (loss : J → D → Bool) (interfaces : List J) : Nat :=
  countListBool distinctions (residualBool required loss interfaces)

/-- A finite distinction presentation covers the distinction domain under study. -/
structure ExhaustiveDistinctionPresentation
    {D : Type u} (distinctions : List D) : Prop where
  distinctions_exhaustive : ∀ d : D, InList d distinctions

/-- Boolean presentation of logical required/loss predicates. -/
structure BooleanLossPresentation
    {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J)
    (required : D → Bool) (loss : J → D → Bool)
    (interfaces : List J) : Prop where
  required_iff : ∀ d : D, required d = true ↔ Required d
  loss_iff : ∀ j : J, ∀ d : D,
    InList j interfaces → (loss j d = true ↔ Loss j d)
  interfaces_complete : ∀ j : J, I j → InList j interfaces
  interfaces_sound : ∀ j : J, InList j interfaces → I j

theorem boolAnd_eq_true_left {a b : Bool} :
    (a && b) = true → a = true := by
  cases a <;> cases b <;> intro h
  · cases h
  · cases h
  · cases h
  · rfl

theorem boolAnd_eq_true_right {a b : Bool} :
    (a && b) = true → b = true := by
  cases a <;> cases b <;> intro h
  · cases h
  · cases h
  · cases h
  · rfl

theorem boolAnd_eq_true_intro {a b : Bool} :
    a = true → b = true → (a && b) = true := by
  intro ha hb
  cases ha
  cases hb
  rfl

theorem bool_eq_false_of_not_true {b : Bool} :
    (b = true → False) → b = false := by
  intro h
  cases b
  · rfl
  · exact False.elim (h rfl)

/-- Boolean all-loss is pointwise truth on the finite interface list. -/
theorem allLossBool_eq_true_iff
    {D : Type u} {J : Type v}
    (loss : J → D → Bool) (interfaces : List J) (d : D) :
    allLossBool loss interfaces d = true ↔
      ∀ j : J, InList j interfaces → loss j d = true := by
  induction interfaces with
  | nil =>
      constructor
      · intro _ j hIn
        cases hIn
      · intro _
        rfl
  | cons j js ih =>
      constructor
      · intro h k hIn
        have hHead : loss j d = true :=
          boolAnd_eq_true_left (a := loss j d) (b := allLossBool loss js d) h
        have hTailAll : allLossBool loss js d = true :=
          boolAnd_eq_true_right (a := loss j d) (b := allLossBool loss js d) h
        cases hIn with
        | head =>
            exact hHead
        | tail hTail =>
            exact (ih.1 hTailAll) k hTail
      · intro h
        have hHead : loss j d = true :=
          h j InList.head
        have hTail : allLossBool loss js d = true :=
          ih.2 (fun k hk => h k (InList.tail hk))
        exact boolAnd_eq_true_intro hHead hTail

/-- Boolean incidence residual equals required plus all listed losses. -/
theorem residualBool_eq_true_iff
    {D : Type u} {J : Type v}
    (required : D → Bool) (loss : J → D → Bool)
    (interfaces : List J) (d : D) :
    residualBool required loss interfaces d = true ↔
      required d = true ∧
        ∀ j : J, InList j interfaces → loss j d = true := by
  constructor
  · intro h
    have hReq : required d = true :=
      boolAnd_eq_true_left
        (a := required d) (b := allLossBool loss interfaces d) h
    have hAll : allLossBool loss interfaces d = true :=
      boolAnd_eq_true_right
        (a := required d) (b := allLossBool loss interfaces d) h
    exact ⟨hReq, (allLossBool_eq_true_iff loss interfaces d).1 hAll⟩
  · intro h
    have hAll : allLossBool loss interfaces d = true :=
      (allLossBool_eq_true_iff loss interfaces d).2 h.2
    exact boolAnd_eq_true_intro h.1 hAll

/-- Zero incidence coordinate means no listed distinction passes the residual test. -/
theorem rhoList_eq_zero_iff_residualBool_empty_on_list
    {D : Type u} {J : Type v}
    (distinctions : List D) (required : D → Bool)
    (loss : J → D → Bool) (interfaces : List J) :
    rhoList distinctions required loss interfaces = 0 ↔
      ∀ d : D, InList d distinctions →
        residualBool required loss interfaces d = false := by
  constructor
  · intro hZero d hIn
    exact bool_eq_false_of_not_true (by
      intro hTrue
      have hPos : 0 <
          countListBool distinctions
            (residualBool required loss interfaces) :=
        countListBool_pos_of_inList_true
          distinctions (residualBool required loss interfaces) d hIn hTrue
      rw [rhoList] at hZero
      rw [hZero] at hPos
      exact Nat.not_lt_zero 0 hPos)
  · intro hEmpty
    have hAllFalse :
        AllFalseBool (residualBool required loss interfaces) distinctions := by
      induction distinctions with
      | nil =>
          exact AllFalseBool.nil
      | cons d ds ih =>
          exact AllFalseBool.cons
            (hEmpty d InList.head)
            (ih (fun e he => hEmpty e (InList.tail he)))
    rw [rhoList]
    exact countListBool_eq_zero_of_allFalseBool
      distinctions (residualBool required loss interfaces) hAllFalse

/--
For an exhaustive finite incidence presentation, positive `rhoList` is exactly
the existence of a common residual witness.
-/
theorem rhoList_pos_iff_commonResidualNonempty
    {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J)
    (distinctions : List D) (required : D → Bool)
    (loss : J → D → Bool) (interfaces : List J)
    (hDist : ExhaustiveDistinctionPresentation distinctions)
    (hBool :
      BooleanLossPresentation Required Loss I required loss interfaces) :
    0 < rhoList distinctions required loss interfaces ↔
      CommonResidualNonempty Required Loss I := by
  constructor
  · intro hPos
    unfold rhoList at hPos
    rcases exists_inList_true_of_countListBool_pos
        distinctions (residualBool required loss interfaces) hPos with
      ⟨d, _hIn, hTrue⟩
    have hResidualBool :
        required d = true ∧
          ∀ j : J, InList j interfaces → loss j d = true :=
      (residualBool_eq_true_iff required loss interfaces d).1 hTrue
    exact
      ⟨d,
        ⟨(hBool.required_iff d).1 hResidualBool.1,
          fun j hj =>
            let hjIn := hBool.interfaces_complete j hj
            let hLossIff : loss j d = true ↔ Loss j d :=
              (hBool.loss_iff j d) hjIn
            hLossIff.1 (hResidualBool.2 j hjIn)⟩⟩
  · intro hNonempty
    rcases hNonempty with ⟨d, hResidual⟩
    have hIn : InList d distinctions :=
      hDist.distinctions_exhaustive d
    have hRequired : required d = true :=
      (hBool.required_iff d).2 hResidual.1
    have hLosses :
        ∀ j : J, InList j interfaces → loss j d = true := by
      intro j hj
      have hLossIff : loss j d = true ↔ Loss j d :=
        (hBool.loss_iff j d) hj
      exact hLossIff.2 (hResidual.2 j (hBool.interfaces_sound j hj))
    have hTrue :
        residualBool required loss interfaces d = true :=
      (residualBool_eq_true_iff required loss interfaces d).2
        ⟨hRequired, hLosses⟩
    unfold rhoList
    exact countListBool_pos_of_inList_true
      distinctions (residualBool required loss interfaces) d hIn hTrue

/--
For an exhaustive finite incidence presentation, `rhoList = 0` is exactly
closure by losses.
-/
theorem rhoList_zero_iff_closedByLoss
    {D : Type u} {J : Type v}
    (Required : D → Prop) (Loss : J → D → Prop)
    (I : Subfamily J)
    (distinctions : List D) (required : D → Bool)
    (loss : J → D → Bool) (interfaces : List J)
    (hDist : ExhaustiveDistinctionPresentation distinctions)
    (hBool :
      BooleanLossPresentation Required Loss I required loss interfaces) :
    rhoList distinctions required loss interfaces = 0 ↔
      ClosedByLoss Required Loss I := by
  constructor
  · intro hZero d hResidual
    have hFalse :
        residualBool required loss interfaces d = false :=
      (rhoList_eq_zero_iff_residualBool_empty_on_list
        distinctions required loss interfaces).1
        hZero d (hDist.distinctions_exhaustive d)
    have hRequired : required d = true :=
      (hBool.required_iff d).2 hResidual.1
    have hLosses :
        ∀ j : J, InList j interfaces → loss j d = true := by
      intro j hj
      have hLossIff : loss j d = true ↔ Loss j d :=
        (hBool.loss_iff j d) hj
      exact hLossIff.2 (hResidual.2 j (hBool.interfaces_sound j hj))
    have hTrue :
        residualBool required loss interfaces d = true :=
      (residualBool_eq_true_iff required loss interfaces d).2
        ⟨hRequired, hLosses⟩
    rw [hTrue] at hFalse
    cases hFalse
  · intro hClosed
    exact
      (rhoList_eq_zero_iff_residualBool_empty_on_list
        distinctions required loss interfaces).2
        (fun d _hIn =>
          bool_eq_false_of_not_true (by
            intro hTrue
            have hResidualBool :
                required d = true ∧
                  ∀ j : J, InList j interfaces → loss j d = true :=
              (residualBool_eq_true_iff required loss interfaces d).1 hTrue
            have hResidual : CommonResidual Required Loss I d := by
              exact
                ⟨(hBool.required_iff d).1 hResidualBool.1,
                  fun j hj =>
                    let hjIn := hBool.interfaces_complete j hj
                    let hLossIff : loss j d = true ↔ Loss j d :=
                      (hBool.loss_iff j d) hjIn
                    hLossIff.1 (hResidualBool.2 j hjIn)⟩
            exact hClosed d hResidual))

end RegimesSelfContained
end Standalone
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.Subfamily
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExplicitPresentationRegime
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.Coherent_R1
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.DiagonalizationWitness
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.Residual_R2
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.Closed_R2
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.closed_R2_iff_residualEmpty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.closed_R2_iff_no_diagonalizationWitness
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.rho
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExhaustiveFiniteResidualPresentation
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.finiteResidualCoordinate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.finiteResidualCoordinate_pos_iff_residualNonempty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.finiteResidualCoordinate_zero_iff_residualEmpty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.finiteResidualCoordinate_zero_iff_closed_R2
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedSame
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedResidual
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedResidualEmpty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatorNonDescentWitness
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.WitnessedIrreducibleMediator
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.witnessedIrreducibleMediator_irreducibleMediator
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedResidualList
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedResidualListBool
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.mediatedRho
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.mediatedFiniteResidualCoordinate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.mediatedFiniteResidualCoordinate_pos_iff_mediatedResidualNonempty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.mediatedFiniteResidualCoordinate_zero_iff_mediatedResidualEmpty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.MediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.WitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.witnessedProperMediatedR2Certificate.toProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.properMediatedR2Certificate.toMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.residualNonempty_not_closed_R2
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.properMediatedR2Certificate_not_closed_R2
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExistsMediatedR2CertificateAtDim
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExistsProperMediatedR2CertificateAtDim
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExactMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExactProperMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.DimensionMinimalMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.DimensionMinimalProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.DimensionMinimalWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.dimensionMinimalProper_of_witnessed
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.exactMediatedR2Dimension_of_dimensionMinimalCertificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.no_smaller_mediatedR2Certificate_of_exactDimension
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.no_smaller_properMediatedR2Certificate_of_exactProperDimension
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.endToEnd_staticProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.endToEnd_staticWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.mediatedResidualEmpty_iff_mediator_separates_witnesses
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.irreducibleMediator_nonDescends_properSubfamily
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.CommonResidual
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.CommonResidualNonempty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ClosedByLoss
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.IrreducibleClosedByLoss
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.closedByLoss_iff_commonResidualEmpty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.rhoList
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.ExhaustiveDistinctionPresentation
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.BooleanLossPresentation
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.rhoList_eq_zero_iff_residualBool_empty_on_list
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.rhoList_pos_iff_commonResidualNonempty
#print axioms LocalSemanticClosure.Standalone.RegimesSelfContained.rhoList_zero_iff_closedByLoss
/- AXIOM_AUDIT_END -/
