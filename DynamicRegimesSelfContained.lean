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
namespace DynamicRegimesSelfContained

universe u v w z a b

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

/-- Direct R2 closure implies residual emptiness; this direction is fully constructive. -/
theorem residualEmpty_of_closed_R2
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed_R2 obs sigma I → ResidualEmpty_R2 obs sigma I := by
  intro hClosed x y hResidual
  exact hResidual.1 (hClosed x y hResidual.2)

/--
Residual emptiness implies direct R2 closure when target equality is decidable.

This is the only direction of `closed_R2_iff_residualEmpty` that needs
`[DecidableEq Y]`.
-/
theorem closed_R2_of_residualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    ResidualEmpty_R2 obs sigma I → Closed_R2 obs sigma I := by
  intro hEmpty x y hSame
  by_cases hEq : sigma x = sigma y
  · exact hEq
  · exact False.elim (hEmpty x y ⟨hEq, hSame⟩)

/-- Direct R2 closure is residual emptiness. -/
theorem closed_R2_iff_residualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed_R2 obs sigma I ↔ ResidualEmpty_R2 obs sigma I := by
  constructor
  · exact residualEmpty_of_closed_R2 obs sigma I
  · exact closed_R2_of_residualEmpty obs sigma I

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

/--
Numerical residual coordinate over explicit lists of states and interfaces.

This is a support coordinate for emptiness/positivity.  If the lists contain
duplicates, the numerical value counts with multiplicity; the certified
properties are `rho = 0` and `0 < rho`.
-/
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

/-- The active family has at least one proper subfamily. -/
def HasProperSubfamily {J : Type u} (I : Subfamily J) : Prop :=
  ∃ K : Subfamily J, Subfamily.Proper K I

/-- Irreducibility: the mediator does not descend to any proper subfamily. -/
def IrreducibleMediator
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  ∀ K : Subfamily J,
    Subfamily.Proper K I → ¬ MediatorDescendsSubfamily obs K M

/--
Non-vacuous irreducibility: irreducibility together with the assertion that
there is at least one proper active subfamily to test.
-/
def NonvacuousIrreducibleMediator
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  HasProperSubfamily I ∧ IrreducibleMediator obs I M

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

/--
Support coordinate for finite mediated residuals.

With duplicate states, the numerical value counts with multiplicity; the
certified properties are zero and positivity.
-/
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

/-- Every point of `Fin 1` has value zero. -/
theorem fin_one_val_eq_zero (a : Fin 1) : a.val = 0 := by
  cases a with
  | mk av ah =>
      cases av with
      | zero =>
          rfl
      | succ av =>
          have hLtZero : av < 0 :=
            Nat.lt_of_succ_lt_succ ah
          exact False.elim (Nat.not_lt_zero av hLtZero)

/-- Any two points of `Fin 1` are equal, constructively. -/
theorem fin_one_eq (a b : Fin 1) : a = b := by
  apply Fin.ext
  cases a with
  | mk av ah =>
      cases b with
      | mk bv bh =>
          exact (fin_one_val_eq_zero ⟨av, ah⟩).trans
            (fin_one_val_eq_zero ⟨bv, bh⟩).symm

/-- No proper mediated R2 certificate exists in dimension `0`. -/
theorem no_properMediatedR2CertificateAtDim_zero
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I 0 := by
  intro hExists
  rcases hExists with ⟨M, hCert⟩
  rcases hCert.residual_exists with ⟨x, _y, _hResidual⟩
  exact Fin.elim0 (M x)

/-- No proper mediated R2 certificate exists in dimension `1`. -/
theorem no_properMediatedR2CertificateAtDim_one
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    ¬ ExistsProperMediatedR2CertificateAtDim obs sigma I 1 := by
  intro hExists
  rcases hExists with ⟨M, hCert⟩
  rcases hCert.residual_exists with ⟨x, y, hResidual⟩
  have hM : M x = M y := fin_one_eq (M x) (M y)
  have hMediatedResidual : MediatedResidual obs sigma I M x y :=
    ⟨hResidual.1, ⟨hResidual.2, hM⟩⟩
  exact hCert.closes x y hMediatedResidual

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

/-- An exact proper mediated R2 dimension is at least two. -/
theorem one_lt_dim_of_exactProperMediatedR2Dimension
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (n : Nat) :
    ExactProperMediatedR2Dimension obs sigma I n → 1 < n := by
  intro hExact
  cases n with
  | zero =>
      exact False.elim
        ((no_properMediatedR2CertificateAtDim_zero obs sigma I)
          hExact.exists_at)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim
            ((no_properMediatedR2CertificateAtDim_one obs sigma I)
              hExact.exists_at)
      | succ n =>
          exact Nat.succ_lt_succ (Nat.succ_pos n)

/-- A dimension-minimal proper mediated R2 certificate has dimension at least two. -/
theorem one_lt_dim_of_dimensionMinimalProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) :
    DimensionMinimalProperMediatedR2Certificate obs sigma I M →
      1 < n := by
  intro hMinimal
  exact one_lt_dim_of_exactProperMediatedR2Dimension obs sigma I n
    (exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
      hMinimal)

/--
A dimension-minimal witnessed proper mediated R2 certificate has dimension at
least two.
-/
theorem one_lt_dim_of_dimensionMinimalWitnessedProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) :
    DimensionMinimalWitnessedProperMediatedR2Certificate obs sigma I M →
      1 < n := by
  intro hMinimal
  exact one_lt_dim_of_dimensionMinimalProperMediatedR2Certificate
    obs sigma I M (dimensionMinimalProper_of_witnessed hMinimal)

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

/--
Support coordinate for finite incidence residuals.

With duplicate distinctions, the numerical value counts with multiplicity; the
certified properties are zero and positivity.
-/
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

/-!
## Dynamic R1/R2 layer

The preceding development is static: a target `sigma : S → Y` is fixed.  The
dynamic layer keeps the static certificate unchanged and indexes the target by
a step, horizon, or query.  Each dynamic step therefore exposes a local R2
problem, while the additional structures below keep track of uniform mediation
and residual transport through time.
-/

/-- A dynamic target is a family of static targets indexed by `Step`. -/
structure DynamicTarget (S : Type v) (Step : Type u) (Y : Type z) where
  targetAt : Step → S → Y

/-- The local diagonal witness at a dynamic step. -/
abbrev DynamicDiagonalizationWitness
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (x y : S) : Prop :=
  DiagonalizationWitness obs (target.targetAt step) I x y

/-- The local dynamic residual at a step. -/
abbrev DynamicResidual_R2
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (x y : S) : Prop :=
  Residual_R2 obs (target.targetAt step) I x y

/-- Local dynamic residual emptiness at a step. -/
abbrev DynamicResidualEmpty_R2
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) : Prop :=
  ResidualEmpty_R2 obs (target.targetAt step) I

/-- Local dynamic residual non-emptiness at a step. -/
abbrev DynamicResidualNonempty_R2
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) : Prop :=
  ResidualNonempty_R2 obs (target.targetAt step) I

/-- Local dynamic direct closure at a step. -/
abbrev DynamicClosed_R2
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) : Prop :=
  Closed_R2 obs (target.targetAt step) I

/-- At each step, local dynamic closure is local residual emptiness. -/
theorem dynamicClosed_R2_iff_dynamicResidualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    [DecidableEq Y]
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) :
    DynamicClosed_R2 obs target I step ↔
      DynamicResidualEmpty_R2 obs target I step :=
  closed_R2_iff_residualEmpty obs (target.targetAt step) I

/-- Local dynamic mediated residual emptiness at a step. -/
abbrev DynamicMediatedResidualEmpty
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (M : S → Fin n) : Prop :=
  MediatedResidualEmpty obs (target.targetAt step) I M

/-- A proper mediated R2 certificate at one dynamic step. -/
abbrev StepwiseProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (M : S → Fin n) : Prop :=
  ProperMediatedR2Certificate obs (target.targetAt step) I M

/-- A witnessed proper mediated R2 certificate at one dynamic step. -/
abbrev StepwiseWitnessedProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (M : S → Fin n) : Prop :=
  WitnessedProperMediatedR2Certificate obs (target.targetAt step) I M

/-- Exact proper mediated dimension at one dynamic step. -/
abbrev DynamicExactProperMediatedR2Dimension
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (n : Nat) : Prop :=
  ExactProperMediatedR2Dimension obs (target.targetAt step) I n

/--
Uniform mediated closure by a step-indexed finite mediator of fixed dimension.

The mediator may depend on the step, but its codomain size `n` is uniform.
-/
structure UniformMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (M : Step → S → Fin n) : Prop where
  closes :
    ∀ step : Step,
      MediatedResidualEmpty obs (target.targetAt step) I (M step)
  irreducible :
    ∀ step : Step,
      IrreducibleMediator obs I (M step)

/--
Uniform proper mediated closure: every dynamic step has a nonempty residual
before mediation, and the step-indexed mediator closes it irreducibly.
-/
structure UniformProperMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (M : Step → S → Fin n) : Prop where
  residual_exists :
    ∀ step : Step,
      ResidualNonempty_R2 obs (target.targetAt step) I
  closes :
    ∀ step : Step,
      MediatedResidualEmpty obs (target.targetAt step) I (M step)
  irreducible :
    ∀ step : Step,
      IrreducibleMediator obs I (M step)

/-- A uniform proper dynamic certificate gives the static certificate at each step. -/
theorem stepwiseProperMediatedR2Certificate_of_uniform
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    {obs : J → S → V} {target : DynamicTarget S Step Y}
    {I : Subfamily J} {M : Step → S → Fin n}
    (h : UniformProperMediatedR2Certificate obs target I M)
    (step : Step) :
    StepwiseProperMediatedR2Certificate obs target I step (M step) :=
  ⟨h.residual_exists step, h.closes step, h.irreducible step⟩

/-- A uniform proper dynamic certificate rules out direct closure at each step. -/
theorem uniformProperMediatedR2Certificate_not_closed_at_step
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    [DecidableEq Y] {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (M : Step → S → Fin n) :
    UniformProperMediatedR2Certificate obs target I M →
      ∀ step : Step, ¬ DynamicClosed_R2 obs target I step := by
  intro h step
  exact residualNonempty_not_closed_R2
    obs (target.targetAt step) I (h.residual_exists step)

/-- A step-indexed compatibility predicate. -/
abbrev DynamicCompatible
    {S : Type v} {Step : Type a}
    (compatible : Step → S → Prop) (step : Step) (x : S) : Prop :=
  compatible step x

/--
A dynamic step separates the active interface fiber when two states remain
jointly indistinguishable by `I`, but only one is compatible with the step.
-/
def StepSeparatesFiber
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) : Prop :=
  ∃ x y : S,
    JointSame obs I x y ∧
      DynamicCompatible compatible step x ∧
        ¬ DynamicCompatible compatible step y

/--
A lag event is the pointed witness form of step separation: the current active
interfaces identify two states, while a future step distinguishes them.
-/
def LagEvent
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step)
    (x y : S) : Prop :=
  JointSame obs I x y ∧
    DynamicCompatible compatible step x ∧
      ¬ DynamicCompatible compatible step y

/-- A pointed lag event yields unpointed step separation. -/
theorem stepSeparatesFiber_of_lagEvent
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    {obs : J → S → V} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step}
    {x y : S} :
    LagEvent obs I compatible step x y →
      StepSeparatesFiber obs I compatible step := by
  intro h
  exact ⟨x, y, h⟩

/-- A lag event necessarily relates two distinct states. -/
theorem ne_of_lagEvent
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    {obs : J → S → V} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step}
    {x y : S} :
    LagEvent obs I compatible step x y → x ≠ y := by
  intro hLag hEq
  cases hEq
  exact hLag.2.2 hLag.2.1

/--
Compatibility dimension: compatibility with a dynamic step is decided by a
finite mediator with `n` values.
-/
def CompatDimLe
    {S : Type v} {Step : Type a}
    (compatible : Step → S → Prop) (step : Step) (n : Nat) : Prop :=
  ∃ (M : S → Fin n) (pred : Fin n → Prop),
    ∀ x : S, DynamicCompatible compatible step x ↔ pred (M x)

/--
A finite refining lift for a dynamic step.  The finite supplement `mediator`
is the only part used to decide compatibility; `base` records the retained
visible reading.
-/
structure RefiningLiftData
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) : Type (max v b a) where
  extObs : S → Base × Fin n
  refines_fst : ∀ x : S, base x = (extObs x).1
  predFin : Fin n → Prop
  factors : ∀ x : S, DynamicCompatible compatible step x ↔ predFin ((extObs x).2)

/-- Existence of a refining lift at finite dimension `n`. -/
abbrev RefiningLift
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) : Prop :=
  Nonempty (RefiningLiftData base compatible step n)

/-- A finite compatibility classifier produces a refining lift. -/
theorem refiningLift_of_compatDimLe
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) :
    CompatDimLe compatible step n →
      RefiningLift base compatible step n := by
  rintro ⟨M, pred, hFactors⟩
  let extObs : S → Base × Fin n := fun x => (base x, M x)
  exact
    ⟨{ extObs := extObs
       refines_fst := by intro x; rfl
       predFin := pred
       factors := by intro x; simpa [extObs] using hFactors x }⟩

/-- A refining lift gives a finite compatibility classifier. -/
theorem compatDimLe_of_refiningLift
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) :
    RefiningLift base compatible step n →
      CompatDimLe compatible step n := by
  rintro ⟨L⟩
  exact ⟨(fun x => (L.extObs x).2), L.predFin, L.factors⟩

/-- Compatibility dimension is equivalent to the existence of a refining lift. -/
theorem compatDimLe_iff_refiningLift
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) :
    CompatDimLe compatible step n ↔ RefiningLift base compatible step n := by
  constructor
  · exact refiningLift_of_compatDimLe base compatible step n
  · exact compatDimLe_of_refiningLift base compatible step n

/-- Exact finite compatibility dimension. -/
def CompatDimEq
    {S : Type v} {Step : Type a}
    (compatible : Step → S → Prop) (step : Step) (n : Nat) : Prop :=
  CompatDimLe compatible step n ∧
    ∀ m : Nat, m < n → ¬ CompatDimLe compatible step m

/-- Exact finite compatibility dimension excludes smaller refining lifts. -/
theorem no_smaller_refiningLift_of_compatDimEq
    {S : Type v} {Base : Type b} {Step : Type a}
    (base : S → Base) (compatible : Step → S → Prop)
    (step : Step) (n : Nat) :
    CompatDimEq compatible step n →
      ∀ m : Nat, m < n → ¬ RefiningLift base compatible step m := by
  intro hEq m hm hLift
  exact hEq.2 m hm
    ((compatDimLe_iff_refiningLift base compatible step m).2 hLift)

/--
A subfamily predicts a dynamic step when some finite readout that descends to
that subfamily decides step compatibility.
-/
def SubfamilyPredictsStep
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (K : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) : Prop :=
  ∃ n : Nat, ∃ readout : S → Fin n,
    MediatorDescendsSubfamily obs K readout ∧
      ∃ pred : Fin n → Prop,
        ∀ x : S, DynamicCompatible compatible step x ↔ pred (readout x)

/-- A dynamic finite mediator descends to a subfamily. -/
def DynamicMediatorDescendsSubfamily
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (M : S → Fin n) : Prop :=
  MediatorDescendsSubfamily obs K M

/--
If the finite supplement of a refining lift descends to a subfamily, that
subfamily predicts the dynamic compatibility truth.
-/
theorem subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
    {J : Type u} {S : Type v} {V : Type w} {Base : Type b} {Step : Type a}
    (obs : J → S → V) (K : Subfamily J)
    (base : S → Base)
    {compatible : Step → S → Prop} {step : Step} {n : Nat}
    (L : RefiningLiftData
      (S := S) (Base := Base) (Step := Step)
      (base := base) (compatible := compatible) step n) :
    DynamicMediatorDescendsSubfamily obs K (fun x : S => (L.extObs x).2) →
      SubfamilyPredictsStep obs K compatible step := by
  intro hDescends
  exact
    ⟨n, (fun x : S => (L.extObs x).2), hDescends,
      L.predFin, L.factors⟩

/-- If a subfamily cannot predict the step, the dynamic mediator cannot descend to it. -/
theorem not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
    {J : Type u} {S : Type v} {V : Type w} {Base : Type b} {Step : Type a}
    (obs : J → S → V) (K : Subfamily J)
    (base : S → Base)
    {compatible : Step → S → Prop} {step : Step} {n : Nat}
    (L : RefiningLiftData
      (S := S) (Base := Base) (Step := Step)
      (base := base) (compatible := compatible) step n) :
    ¬ SubfamilyPredictsStep obs K compatible step →
      ¬ DynamicMediatorDescendsSubfamily obs K (fun x : S => (L.extObs x).2) := by
  intro hNoPredict hDescends
  exact hNoPredict
    (subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
      obs K base L hDescends)

/--
A dynamic family profile: at a step, the residual exists, the mediator closes it,
and the mediator does not descend to any proper active subfamily.
-/
structure FamilyIrreducibleDynamicMediationProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    (obs : J → S → V) (target : DynamicTarget S Step Y)
    (I : Subfamily J) (step : Step) (M : S → Fin n) : Prop where
  residual_exists :
    ResidualNonempty_R2 obs (target.targetAt step) I
  closes :
    MediatedResidualEmpty obs (target.targetAt step) I M
  no_descent :
    ∀ K : Subfamily J,
      Subfamily.Proper K I → ¬ MediatorDescendsSubfamily obs K M

/-- The dynamic family profile gives a proper mediated R2 certificate at the step. -/
theorem properMediatedR2Certificate_of_familyIrreducibleDynamicProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    {obs : J → S → V} {target : DynamicTarget S Step Y}
    {I : Subfamily J} {step : Step} {M : S → Fin n} :
    FamilyIrreducibleDynamicMediationProfile obs target I step M →
      StepwiseProperMediatedR2Certificate obs target I step M := by
  intro h
  exact ⟨h.residual_exists, h.closes, h.no_descent⟩

/-- A proper mediated R2 certificate gives the dynamic family profile at the step. -/
theorem familyIrreducibleDynamicProfile_of_properMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    {obs : J → S → V} {target : DynamicTarget S Step Y}
    {I : Subfamily J} {step : Step} {M : S → Fin n} :
    StepwiseProperMediatedR2Certificate obs target I step M →
      FamilyIrreducibleDynamicMediationProfile obs target I step M := by
  intro h
  exact ⟨h.residual_exists, h.closes, h.irreducible⟩

/-- The dynamic family profile is equivalent to a proper mediated R2 certificate at the step. -/
theorem familyIrreducibleDynamicProfile_iff_properMediatedR2Certificate
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a} {Y : Type z}
    {n : Nat}
    {obs : J → S → V} {target : DynamicTarget S Step Y}
    {I : Subfamily J} {step : Step} {M : S → Fin n} :
    FamilyIrreducibleDynamicMediationProfile obs target I step M ↔
      StepwiseProperMediatedR2Certificate obs target I step M := by
  constructor
  · exact properMediatedR2Certificate_of_familyIrreducibleDynamicProfile
  · exact familyIrreducibleDynamicProfile_of_properMediatedR2Certificate

/--
Compatibility-oriented dynamic family profile.

The step separates the active fiber and has exact finite compatibility
dimension. Prediction failure for every subfamily of the active family is
derived from the separation witness.
-/
structure FamilyIrreducibleCompatibilityProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) (n : Nat) : Prop where
  separates :
    StepSeparatesFiber obs I compatible step
  exact_dim :
    CompatDimEq compatible step n

/-- Indistinguishability by `I` restricts to any subfamily `K ⊆ I`. -/
theorem jointSame_of_subset
    {J : Type u} {S : Type v} {V : Type w}
    {obs : J → S → V} {K I : Subfamily J} {x y : S} :
    Subfamily.Subset K I →
      JointSame obs I x y →
        JointSame obs K x y := by
  intro hSubset hSameI j hj
  exact hSameI j (hSubset j hj)

/--
If a step already separates an active fiber, no subfamily of the active family
can predict the step truth through a descending finite readout.
-/
theorem subfamilyPrediction_excluded_of_stepSeparatesFiber
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) :
    StepSeparatesFiber obs I compatible step →
      ∀ K : Subfamily J,
        Subfamily.Subset K I →
          ¬ SubfamilyPredictsStep obs K compatible step := by
  intro hSeparate K hSubset hPredict
  rcases hSeparate with ⟨x, y, hSameI, hCompatX, hNotCompatY⟩
  rcases hPredict with ⟨n, readout, hDescends, pred, hFactors⟩
  have hSameK : JointSame obs K x y := jointSame_of_subset hSubset hSameI
  have hReadout : readout x = readout y := hDescends x y hSameK
  have hPredX : pred (readout x) := (hFactors x).1 hCompatX
  have hCompatY : DynamicCompatible compatible step y := by
    exact (hFactors y).2 (by simpa [hReadout] using hPredX)
  exact hNotCompatY hCompatY

/--
A separated compatibility fiber cannot be classified through a zero-dimensional
finite readout.
-/
theorem not_compatDimLe_zero_of_stepSeparatesFiber
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) :
    StepSeparatesFiber obs I compatible step →
      ¬ CompatDimLe compatible step 0 := by
  intro hSeparate hDim
  rcases hSeparate with ⟨x, _y, _hSame, _hCompatX, _hNotCompatY⟩
  rcases hDim with ⟨M, _pred, _hFactors⟩
  exact Fin.elim0 (M x)

/--
A separated compatibility fiber cannot be classified through a one-dimensional
finite readout.
-/
theorem not_compatDimLe_one_of_stepSeparatesFiber
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    (obs : J → S → V) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) :
    StepSeparatesFiber obs I compatible step →
      ¬ CompatDimLe compatible step 1 := by
  intro hSeparate hDim
  rcases hSeparate with ⟨x, y, _hSame, hCompatX, hNotCompatY⟩
  rcases hDim with ⟨M, pred, hFactors⟩
  have hMxMy : M x = M y := fin_one_eq (M x) (M y)
  have hPredX : pred (M x) := (hFactors x).1 hCompatX
  have hCompatY : DynamicCompatible compatible step y := by
    exact (hFactors y).2 (by simpa [hMxMy] using hPredX)
  exact hNotCompatY hCompatY

/-- A family-irreducible compatibility profile has strictly positive dimension. -/
theorem positive_dim_of_familyIrreducibleCompatibilityProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    {obs : J → S → V} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step} {n : Nat} :
    FamilyIrreducibleCompatibilityProfile obs I compatible step n →
      0 < n := by
  intro hProfile
  cases n with
  | zero =>
      exact False.elim
        ((not_compatDimLe_zero_of_stepSeparatesFiber
          obs I compatible step hProfile.separates)
          hProfile.exact_dim.1)
  | succ n =>
      exact Nat.succ_pos n

/-- A family-irreducible compatibility profile has dimension at least two. -/
theorem one_lt_dim_of_familyIrreducibleCompatibilityProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    {obs : J → S → V} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step} {n : Nat} :
    FamilyIrreducibleCompatibilityProfile obs I compatible step n →
      1 < n := by
  intro hProfile
  cases n with
  | zero =>
      exact False.elim
        ((not_compatDimLe_zero_of_stepSeparatesFiber
          obs I compatible step hProfile.separates)
          hProfile.exact_dim.1)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim
            ((not_compatDimLe_one_of_stepSeparatesFiber
              obs I compatible step hProfile.separates)
              hProfile.exact_dim.1)
      | succ n =>
          exact Nat.succ_lt_succ (Nat.succ_pos n)

/-- A compatibility profile excludes prediction from every active subfamily. -/
theorem no_subfamilyPrediction_of_familyIrreducibleCompatibilityProfile
    {J : Type u} {S : Type v} {V : Type w} {Step : Type a}
    {obs : J → S → V} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step} {n : Nat} :
    FamilyIrreducibleCompatibilityProfile obs I compatible step n →
      ∀ K : Subfamily J,
        Subfamily.Subset K I →
          ¬ SubfamilyPredictsStep obs K compatible step := by
  intro hProfile K hSubset
  exact subfamilyPrediction_excluded_of_stepSeparatesFiber
    obs I compatible step hProfile.separates K hSubset

/--
Stronger end-to-end dynamic access theorem: a compatibility profile gives a
refining lift at the certified dimension, excludes smaller lifts, and blocks
descent of any exact-dimension lift to every subfamily included in the active
family.
-/
theorem endToEnd_familyIrreducibleCompatibilityProfile_subset
    {J : Type u} {S : Type v} {V : Type w} {Base : Type b} {Step : Type a}
    (obs : J → S → V) (base : S → Base) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) (n : Nat) :
    FamilyIrreducibleCompatibilityProfile obs I compatible step n →
      StepSeparatesFiber obs I compatible step
        ∧ RefiningLift base compatible step n
        ∧ (∀ m : Nat, m < n → ¬ RefiningLift base compatible step m)
        ∧ (∀ L : RefiningLiftData
              (S := S) (Base := Base) (Step := Step)
              (base := base) (compatible := compatible) step n,
            ∀ K : Subfamily J, Subfamily.Subset K I →
              ¬ DynamicMediatorDescendsSubfamily obs K
                (fun x : S => (L.extObs x).2)) := by
  intro hProfile
  refine ⟨hProfile.separates, ?_, ?_, ?_⟩
  · exact (compatDimLe_iff_refiningLift base compatible step n).1
      hProfile.exact_dim.1
  · exact no_smaller_refiningLift_of_compatDimEq
      base compatible step n hProfile.exact_dim
  · intro L K hSubset
    exact not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
      obs K base L
      (subfamilyPrediction_excluded_of_stepSeparatesFiber
        obs I compatible step hProfile.separates K hSubset)

/-- Direct projection of the subset non-descent block from a compatibility profile. -/
theorem no_descent_of_familyIrreducibleCompatibilityProfile_subset
    {J : Type u} {S : Type v} {V : Type w} {Base : Type b} {Step : Type a}
    {obs : J → S → V} {base : S → Base} {I : Subfamily J}
    {compatible : Step → S → Prop} {step : Step} {n : Nat}
    (hProfile : FamilyIrreducibleCompatibilityProfile obs I compatible step n)
    (L : RefiningLiftData
      (S := S) (Base := Base) (Step := Step)
      (base := base) (compatible := compatible) step n)
    (K : Subfamily J) :
    Subfamily.Subset K I →
      ¬ DynamicMediatorDescendsSubfamily obs K
        (fun x : S => (L.extObs x).2) := by
  intro hSubset
  exact
    (endToEnd_familyIrreducibleCompatibilityProfile_subset
      obs base I compatible step n hProfile).2.2.2 L K hSubset

/--
End-to-end dynamic access theorem for proper active subfamilies, kept as the
direct public corollary of the stronger subset theorem.
-/
theorem endToEnd_familyIrreducibleCompatibilityProfile
    {J : Type u} {S : Type v} {V : Type w} {Base : Type b} {Step : Type a}
    (obs : J → S → V) (base : S → Base) (I : Subfamily J)
    (compatible : Step → S → Prop) (step : Step) (n : Nat) :
    FamilyIrreducibleCompatibilityProfile obs I compatible step n →
      StepSeparatesFiber obs I compatible step
        ∧ RefiningLift base compatible step n
        ∧ (∀ m : Nat, m < n → ¬ RefiningLift base compatible step m)
        ∧ (∀ L : RefiningLiftData
              (S := S) (Base := Base) (Step := Step)
              (base := base) (compatible := compatible) step n,
            ∀ K : Subfamily J, Subfamily.Proper K I →
              ¬ DynamicMediatorDescendsSubfamily obs K
                (fun x : S => (L.extObs x).2)) := by
  intro hProfile
  rcases endToEnd_familyIrreducibleCompatibilityProfile_subset
    obs base I compatible step n hProfile with
    ⟨hSeparate, hLift, hNoSmaller, hNoDescendsSubset⟩
  exact
    ⟨hSeparate,
      hLift,
      hNoSmaller,
      fun L K hProper => hNoDescendsSubset L K hProper.1⟩

/-!
### Dynamic residual profiles

The next structures keep genuine temporal data: windows, horizons, dynamic time,
transport, and explicit residual witnesses.  This prevents a dynamic residual
from being collapsed into a detached scalar coordinate.
-/

/--
Abstract dynamic residual profile.

`ResidualAt r W x` says that state `x` is a residual witness at horizon `r` in
window `W`.
-/
structure DynamicResidualProfile
    (State : Type u) (Horizon : Type v) (DynamicTime : Type w)
    (Window : Type z) : Type (max u v w z) where
  stepState : State → State
  nextHorizon : Horizon → Horizon
  nextTime : DynamicTime → DynamicTime
  InWindow : Window → State → Prop
  WindowLe : Window → Window → Prop
  ResidualAt : Horizon → Window → State → Prop
  restrict :
    ∀ {r : Horizon} {W W' : Window} {x : State},
      WindowLe W W' →
        InWindow W x →
          ResidualAt r W' x →
            ResidualAt r W x
  persist :
    ∀ {r : Horizon} {W : Window} {x : State},
      ResidualAt (nextHorizon r) W x →
        ResidualAt r W x
  transport :
    ∀ {r : Horizon} {W : Window} {x : State},
      ResidualAt (nextHorizon r) W x →
        ∃ W' : Window, InWindow W' (stepState x) ∧ ResidualAt r W' (stepState x)

/-- Restrict a dynamic residual witness from a larger window to a smaller one. -/
theorem residualAt_restrict
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window)
    {r : Horizon} {W W' : Window} {x : State} :
    profile.WindowLe W W' →
      profile.InWindow W x →
        profile.ResidualAt r W' x →
          profile.ResidualAt r W x := by
  exact profile.restrict

/-- Persist a future residual witness back to the current horizon. -/
theorem residualAt_persist
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window)
    {r : Horizon} {W : Window} {x : State} :
    profile.ResidualAt (profile.nextHorizon r) W x →
      profile.ResidualAt r W x := by
  exact profile.persist

/-- Transport a future residual witness through one dynamic state step. -/
theorem residualAt_transport
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window)
    {r : Horizon} {W : Window} {x : State} :
    profile.ResidualAt (profile.nextHorizon r) W x →
      ∃ W' : Window,
        profile.InWindow W' (profile.stepState x) ∧
          profile.ResidualAt r W' (profile.stepState x) := by
  exact profile.transport

/--
Finite local coordinate carried by a dynamic residual profile.

The coordinate is tied to witnesses in both directions: positivity exposes a
witness, and every listed witness forces positivity.
-/
structure DynamicResidualCoordinate
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window) :
    Type (max u v w z) where
  rhoAt : Horizon → Window → Nat
  positive_of_residual :
    ∀ {r : Horizon} {W : Window} {x : State},
      profile.InWindow W x →
        profile.ResidualAt r W x →
          0 < rhoAt r W
  witness_of_positive :
    ∀ {r : Horizon} {W : Window},
      0 < rhoAt r W →
        ∃ x : State, profile.InWindow W x ∧ profile.ResidualAt r W x

/-- A zero local coordinate excludes every residual witness in that window. -/
theorem no_residualAt_of_rhoAt_eq_zero
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (coordinate : DynamicResidualCoordinate profile)
    {r : Horizon} {W : Window} {x : State} :
    coordinate.rhoAt r W = 0 →
      profile.InWindow W x →
        ¬ profile.ResidualAt r W x := by
  intro hZero hIn hResidual
  have hPositive : 0 < coordinate.rhoAt r W :=
    coordinate.positive_of_residual hIn hResidual
  rw [hZero] at hPositive
  exact Nat.not_lt_zero 0 hPositive

/-- Positivity of the coordinate is equivalent to an explicit residual witness. -/
theorem rhoAt_pos_iff_exists_residualAt
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (coordinate : DynamicResidualCoordinate profile)
    (r : Horizon) (W : Window) :
    0 < coordinate.rhoAt r W ↔
      ∃ x : State, profile.InWindow W x ∧ profile.ResidualAt r W x := by
  constructor
  · intro hPositive
    exact coordinate.witness_of_positive hPositive
  · intro hWitness
    rcases hWitness with ⟨x, hIn, hResidual⟩
    exact coordinate.positive_of_residual hIn hResidual

/--
Stable residual section.

This is the dynamic non-closure object: it carries a window and a residual
witness through dynamic time.
-/
structure StableResidualSection
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window) :
    Type (max u v w z) where
  windowAt : Horizon → DynamicTime → Window
  stateAt : DynamicTime → State
  stateInWindow :
    ∀ r : Horizon, ∀ k : DynamicTime,
      profile.InWindow (windowAt r k) (stateAt k)
  residualAt :
    ∀ r : Horizon, ∀ k : DynamicTime,
      profile.ResidualAt r (windowAt r k) (stateAt k)
  transitionCompatible :
    ∀ k : DynamicTime,
      stateAt (profile.nextTime k) = profile.stepState (stateAt k)

/-- A stable section transports residual witnesses along the dynamic time axis. -/
theorem stableResidualSection_transport
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (stableSection : StableResidualSection profile)
    (r : Horizon) (k : DynamicTime) :
    ∃ W' : Window,
      profile.InWindow W' (stableSection.stateAt (profile.nextTime k)) ∧
        profile.ResidualAt r W' (stableSection.stateAt (profile.nextTime k)) := by
  rcases profile.transport (stableSection.residualAt (profile.nextHorizon r) k) with
    ⟨W', hIn, hResidual⟩
  refine ⟨W', ?_, ?_⟩
  · rw [stableSection.transitionCompatible k]
    exact hIn
  · rw [stableSection.transitionCompatible k]
    exact hResidual

/-- A stable section persists backward along the horizon axis. -/
theorem stableResidualSection_persist
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (stableSection : StableResidualSection profile)
    (r : Horizon) (k : DynamicTime) :
    profile.ResidualAt r
      (stableSection.windowAt (profile.nextHorizon r) k)
      (stableSection.stateAt k) := by
  exact profile.persist
    (stableSection.residualAt (profile.nextHorizon r) k)

/-- A stable section can be restricted to any smaller window containing the same witness. -/
theorem stableResidualSection_restrict
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (stableSection : StableResidualSection profile)
    {W : Window} (r : Horizon) (k : DynamicTime) :
    profile.WindowLe W (stableSection.windowAt r k) →
      profile.InWindow W (stableSection.stateAt k) →
        profile.ResidualAt r W (stableSection.stateAt k) := by
  intro hLe hIn
  exact profile.restrict hLe hIn (stableSection.residualAt r k)

/-- Every point of a stable section has positive local coordinate. -/
theorem rhoAt_pos_of_stableResidualSection
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (coordinate : DynamicResidualCoordinate profile)
    (stableSection : StableResidualSection profile)
    (r : Horizon) (k : DynamicTime) :
    0 < coordinate.rhoAt r (stableSection.windowAt r k) := by
  exact coordinate.positive_of_residual
    (stableSection.stateInWindow r k)
    (stableSection.residualAt r k)

/-- Absence of a stable residual section. -/
def NoStableResidualSection
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window) : Prop :=
  StableResidualSection profile → False

/--
Constructive bridge from stable dynamic non-closure data to global closure.

Global non-closure is represented as data, because constructively it must carry
enough information to extract a stable residual section.
-/
structure DynamicResidualClosureBridge
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    (profile : DynamicResidualProfile State Horizon DynamicTime Window) :
    Type (max u v w z + 1) where
  GlobalClosure : Prop
  GlobalNonClosure : Type (max u v w z)
  stableSectionOfNonClosure :
    GlobalNonClosure → StableResidualSection profile
  closureOfNoGlobalNonClosure :
    (GlobalNonClosure → False) → GlobalClosure

/-- Absence of global non-closure relative to a dynamic closure bridge. -/
def NoGlobalNonClosure
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (bridge : DynamicResidualClosureBridge profile) : Prop :=
  bridge.GlobalNonClosure → False

/-- If stable residual sections are impossible, global non-closure is impossible. -/
theorem noGlobalNonClosure_of_noStableResidualSection
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (bridge : DynamicResidualClosureBridge profile) :
    NoStableResidualSection profile →
      NoGlobalNonClosure bridge := by
  intro hNoStable hNonClosure
  exact hNoStable (bridge.stableSectionOfNonClosure hNonClosure)

/-- Constructive global closure factors through absence of global non-closure. -/
theorem globalClosure_of_noStableResidualSection
    {State : Type u} {Horizon : Type v} {DynamicTime : Type w}
    {Window : Type z}
    {profile : DynamicResidualProfile State Horizon DynamicTime Window}
    (bridge : DynamicResidualClosureBridge profile) :
    NoStableResidualSection profile →
      bridge.GlobalClosure := by
  intro hNoStable
  exact bridge.closureOfNoGlobalNonClosure
    (noGlobalNonClosure_of_noStableResidualSection bridge hNoStable)

end DynamicRegimesSelfContained
end Standalone
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.Subfamily
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExplicitPresentationRegime
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.Coherent_R1
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DiagonalizationWitness
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.Residual_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.Closed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.residualEmpty_of_closed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.closed_R2_of_residualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.closed_R2_iff_residualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.closed_R2_iff_no_diagonalizationWitness
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rho
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExhaustiveFiniteResidualPresentation
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.finiteResidualCoordinate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.finiteResidualCoordinate_pos_iff_residualNonempty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.finiteResidualCoordinate_zero_iff_residualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.finiteResidualCoordinate_zero_iff_closed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedSame
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedResidual
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedResidualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.HasProperSubfamily
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.NonvacuousIrreducibleMediator
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatorNonDescentWitness
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.WitnessedIrreducibleMediator
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.witnessedIrreducibleMediator_irreducibleMediator
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedResidualList
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedResidualListBool
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.mediatedRho
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.mediatedFiniteResidualCoordinate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.mediatedFiniteResidualCoordinate_pos_iff_mediatedResidualNonempty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.mediatedFiniteResidualCoordinate_zero_iff_mediatedResidualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.MediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.WitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.witnessedProperMediatedR2Certificate.toProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.properMediatedR2Certificate.toMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.residualNonempty_not_closed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.properMediatedR2Certificate_not_closed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExistsMediatedR2CertificateAtDim
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExistsProperMediatedR2CertificateAtDim
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.fin_one_val_eq_zero
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.fin_one_eq
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_properMediatedR2CertificateAtDim_zero
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_properMediatedR2CertificateAtDim_one
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExactMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExactProperMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DimensionMinimalMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DimensionMinimalProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DimensionMinimalWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.dimensionMinimalProper_of_witnessed
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.exactMediatedR2Dimension_of_dimensionMinimalCertificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_smaller_mediatedR2Certificate_of_exactDimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_smaller_properMediatedR2Certificate_of_exactProperDimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.one_lt_dim_of_exactProperMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.one_lt_dim_of_dimensionMinimalProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.one_lt_dim_of_dimensionMinimalWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.endToEnd_staticProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.endToEnd_staticWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.mediatedResidualEmpty_iff_mediator_separates_witnesses
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.irreducibleMediator_nonDescends_properSubfamily
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.CommonResidual
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.CommonResidualNonempty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ClosedByLoss
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.IrreducibleClosedByLoss
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.closedByLoss_iff_commonResidualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoList
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ExhaustiveDistinctionPresentation
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.BooleanLossPresentation
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoList_eq_zero_iff_residualBool_empty_on_list
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoList_pos_iff_commonResidualNonempty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoList_zero_iff_closedByLoss
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicTarget
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicDiagonalizationWitness
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicResidual_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicResidualEmpty_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicClosed_R2
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.dynamicClosed_R2_iff_dynamicResidualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicMediatedResidualEmpty
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.StepwiseProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.StepwiseWitnessedProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicExactProperMediatedR2Dimension
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.UniformMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.UniformProperMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.stepwiseProperMediatedR2Certificate_of_uniform
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.uniformProperMediatedR2Certificate_not_closed_at_step
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicCompatible
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.StepSeparatesFiber
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.LagEvent
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.stepSeparatesFiber_of_lagEvent
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.ne_of_lagEvent
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.CompatDimLe
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.RefiningLiftData
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.RefiningLift
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.refiningLift_of_compatDimLe
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.compatDimLe_of_refiningLift
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.compatDimLe_iff_refiningLift
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.CompatDimEq
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_smaller_refiningLift_of_compatDimEq
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.SubfamilyPredictsStep
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicMediatorDescendsSubfamily
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.FamilyIrreducibleDynamicMediationProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.properMediatedR2Certificate_of_familyIrreducibleDynamicProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.familyIrreducibleDynamicProfile_of_properMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.familyIrreducibleDynamicProfile_iff_properMediatedR2Certificate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.FamilyIrreducibleCompatibilityProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.jointSame_of_subset
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.subfamilyPrediction_excluded_of_stepSeparatesFiber
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.not_compatDimLe_zero_of_stepSeparatesFiber
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.not_compatDimLe_one_of_stepSeparatesFiber
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.positive_dim_of_familyIrreducibleCompatibilityProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.one_lt_dim_of_familyIrreducibleCompatibilityProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_subfamilyPrediction_of_familyIrreducibleCompatibilityProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.endToEnd_familyIrreducibleCompatibilityProfile_subset
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_descent_of_familyIrreducibleCompatibilityProfile_subset
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.endToEnd_familyIrreducibleCompatibilityProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicResidualProfile
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.residualAt_restrict
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.residualAt_persist
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.residualAt_transport
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicResidualCoordinate
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.no_residualAt_of_rhoAt_eq_zero
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoAt_pos_iff_exists_residualAt
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.StableResidualSection
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.stableResidualSection_transport
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.stableResidualSection_persist
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.stableResidualSection_restrict
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.rhoAt_pos_of_stableResidualSection
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.NoStableResidualSection
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.DynamicResidualClosureBridge
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.NoGlobalNonClosure
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.noGlobalNonClosure_of_noStableResidualSection
#print axioms LocalSemanticClosure.Standalone.DynamicRegimesSelfContained.globalClosure_of_noStableResidualSection
/- AXIOM_AUDIT_END -/
