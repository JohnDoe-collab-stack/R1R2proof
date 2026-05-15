import R1R2Notation

/-!
# Zorn as R1/R2 closure with preserved trajectory data

This file does not prove Zorn's lemma from first principles.

It takes the ordinary Zorn conclusion,

```text
there exists a maximal element,
```

and rewrites it in the R1/R2 notation of this project.

For a relation `le : P -> P -> Prop`, the local carrier above `p` is:

```lean
ExtensionCarrier le p := { q : P // le p q }
```

R1 observes only that an element is an admissible extension of `p`, so all
local extensions have the same R1 observation.  R2 reads the actual extension:

```lean
sigma le p x = x.val
```

The main static equivalence is:

```text
local R1/R2 closure at p  <->  p is maximal.
```

Thus Zorn's conclusion can be read as the existence of a point where every
R1-admissible extension has already collapsed to the same R2 value as the
base point.

In this reading, Zorn/choice polarizes the symmetric R1 field of admissible
extensions.  Before the terminal point is chosen, R1 treats local admissible
extensions as observationally identical.  At a terminal point `p`, the point
itself becomes a pole: every still-admissible extension has the same R2 value
as the base extension at `p`.

The second part adds the temporal layer.  A dynamic Zorn certificate is not
just a terminal static maximal point: it also contains a trajectory/history
bounded by the terminal point.  The file proves that this dynamic certificate
preserves exactly the advertised information by giving an equivalence:

```lean
DynamicZornCertificate le hRefl Time
  ≃ StaticWithTrajectoryCertificate le hRefl Time
```

So the dynamic certificate is precisely:

```text
static R1/R2 Zorn closure + compatible trajectory data.
```

Finally, a finite two-point example shows that forgetting the trajectory is
not injective.  This formally exhibits the information lost by the classical
terminal-only reading.

Constructive throughout: quotient-free, `Classical`-free, and `propext`-free.
-/

namespace LocalSemanticClosure
namespace ZornR1R2

open Standalone.RegimesSelfContained
open R1R2Notation

universe u v

/-- A chain for an arbitrary relation: any two elements of the subset compare. -/
def IsChain {P : Type u} (le : P → P → Prop) (C : P → Prop) : Prop :=
  ∀ a : P, C a → ∀ b : P, C b → le a b ∨ le b a

/-- `u` is an upper bound for the subset `C`. -/
def UpperBound {P : Type u} (le : P → P → Prop) (C : P → Prop) (u : P) :
    Prop :=
  ∀ c : P, C c → le c u

/-- Maximality in the equality-collapse form used by the local R1/R2 closure. -/
def Maximal {P : Type u} (le : P → P → Prop) (p : P) : Prop :=
  ∀ q : P, le p q → q = p

/-- The Zorn principle, kept as an external hypothesis rather than reproved. -/
def ZornPrinciple {P : Type u} (le : P → P → Prop) : Prop :=
  (∀ C : P → Prop, IsChain le C → ∃ u : P, UpperBound le C u) →
    ∃ p : P, Maximal le p

/-- Local carrier of extensions above `p`. -/
abbrev ExtensionCarrier {P : Type u} (le : P → P → Prop) (p : P) : Type u :=
  { q : P // le p q }

/-- The base extension is `p` itself. -/
def base {P : Type u} {le : P → P → Prop}
    (hRefl : ∀ p : P, le p p) (p : P) : ExtensionCarrier le p :=
  ⟨p, hRefl p⟩

/-- R1 observes no internal distinction among local extensions. -/
def obs {P : Type u} (le : P → P → Prop) (p : P) :
    Unit → ExtensionCarrier le p → Unit :=
  fun _ _ => ()

/-- The single active R1 extension interface. -/
def I_extension : Subfamily Unit :=
  fun _ => True

/-- R2 reads the actual extension. -/
def sigma {P : Type u} (le : P → P → Prop) (p : P) :
    ExtensionCarrier le p → P :=
  fun x => x.val

/--
Local R1/R2 closure at `p`: every R1-admissible local extension is already
R2-identical to the base point.
-/
def LocalR1R2Closed {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) : Prop :=
  ∀ x : ExtensionCarrier le p,
    (base hRefl p ≡ᵢ[obs le p, I_extension] x)
      ∧ sigma le p x = sigma le p (base hRefl p)

/-- Any two local extensions are R1-identical, because R1 reads only admissibility. -/
theorem observationalIdentity_base_extension
    {P : Type u} {le : P → P → Prop}
    (hRefl : ∀ p : P, le p p) (p : P)
    (x : ExtensionCarrier le p) :
    base hRefl p ≡ᵢ[obs le p, I_extension] x := by
  intro j _hj
  cases j
  rfl

/-- The same R1 identity in the reverse order. -/
theorem observationalIdentity_extension_base
    {P : Type u} {le : P → P → Prop}
    (hRefl : ∀ p : P, le p p) (p : P)
    (x : ExtensionCarrier le p) :
    x ≡ᵢ[obs le p, I_extension] base hRefl p := by
  intro j _hj
  cases j
  rfl

/-- Local R1/R2 closure is exactly maximality. -/
theorem localR1R2Closed_iff_maximal
    {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) :
    LocalR1R2Closed le hRefl p ↔ Maximal le p := by
  constructor
  · intro hClosed q hpq
    exact (hClosed ⟨q, hpq⟩).2
  · intro hMax x
    exact
      ⟨observationalIdentity_base_extension hRefl p x,
        hMax x.val x.property⟩

/-- Existence of a maximal point is exactly existence of a local R1/R2 closure. -/
theorem existsMaximal_iff_existsLocalR1R2Closed
    {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) :
    (∃ p : P, Maximal le p) ↔
      ∃ p : P, LocalR1R2Closed le hRefl p := by
  constructor
  · intro h
    rcases h with ⟨p, hMax⟩
    exact ⟨p, (localR1R2Closed_iff_maximal le hRefl p).2 hMax⟩
  · intro h
    rcases h with ⟨p, hClosed⟩
    exact ⟨p, (localR1R2Closed_iff_maximal le hRefl p).1 hClosed⟩

/-- Zorn's external conclusion rewritten directly as local R1/R2 closure. -/
theorem zorn_as_r1r2_closure
    {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p)
    (zorn : ZornPrinciple le)
    (chain_upper_bound :
      ∀ C : P → Prop, IsChain le C → ∃ u : P, UpperBound le C u) :
    ∃ p : P, LocalR1R2Closed le hRefl p := by
  exact (existsMaximal_iff_existsLocalR1R2Closed le hRefl).1
    (zorn chain_upper_bound)

/--
A strict local extension is an extension whose R2 value differs from the base
point.
-/
def StrictLocalExtension {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) : Prop :=
  ∃ x : ExtensionCarrier le p,
    R2Fracture (sigma le p) x (base hRefl p)

/-- A strict local extension gives a nonempty R1/R2 residual. -/
theorem residualNonempty_of_strictLocalExtension
    {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) :
    StrictLocalExtension le hRefl p →
      ResidualNonempty_R2 (obs le p) (sigma le p) I_extension := by
  intro hStrict
  rcases hStrict with ⟨x, hFrac⟩
  exact
    ⟨x, base hRefl p,
      hFrac,
      observationalIdentity_extension_base hRefl p x⟩

/-- A nonempty local R1/R2 residual gives a strict local extension. -/
theorem strictLocalExtension_of_residualNonempty
    {P : Type u} [DecidableEq P] (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) :
    ResidualNonempty_R2 (obs le p) (sigma le p) I_extension →
      StrictLocalExtension le hRefl p := by
  intro hResidual
  rcases hResidual with ⟨x, y, hDist, _hSame⟩
  by_cases hx : sigma le p x = sigma le p (base hRefl p)
  · exact
      ⟨y, by
        intro hy
        exact hDist (hx.trans hy.symm)⟩
  · exact ⟨x, hx⟩

/-- Local residual nonemptiness is exactly existence of a strict local extension. -/
theorem residualNonempty_iff_strictLocalExtension
    {P : Type u} [DecidableEq P] (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (p : P) :
    ResidualNonempty_R2 (obs le p) (sigma le p) I_extension ↔
      StrictLocalExtension le hRefl p := by
  constructor
  · exact strictLocalExtension_of_residualNonempty le hRefl p
  · exact residualNonempty_of_strictLocalExtension le hRefl p

/-- A dynamic trajectory of extensions. -/
structure ExtensionTrajectory {P : Type u}
    (le : P → P → Prop) (Time : Type v) where
  TimeLe : Time → Time → Prop
  state : Time → P
  monotone : ∀ t u : Time, TimeLe t u → le (state t) (state u)

/-- The trajectory is bounded by a terminal point. -/
def BoundedByTerminal {P : Type u} (le : P → P → Prop)
    {Time : Type v} (terminal : P)
    (trajectory : ExtensionTrajectory le Time) : Prop :=
  ∀ t : Time, le (trajectory.state t) terminal

/-- The static terminal-only Zorn/R1R2 certificate. -/
structure StaticZornCertificate {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) where
  terminal : P
  localClosure : LocalR1R2Closed le hRefl terminal

/--
The dynamic certificate: terminal closure plus the trajectory/history that is
bounded by the terminal.
-/
structure DynamicZornCertificate {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (Time : Type v) where
  terminal : P
  localClosure : LocalR1R2Closed le hRefl terminal
  trajectory : ExtensionTrajectory le Time
  boundedByTerminal : BoundedByTerminal le terminal trajectory

/-- Static closure together with a compatible trajectory. -/
structure StaticWithTrajectoryCertificate {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (Time : Type v) where
  static : StaticZornCertificate le hRefl
  trajectory : ExtensionTrajectory le Time
  boundedByTerminal : BoundedByTerminal le static.terminal trajectory

/-- A local equivalence structure, avoiding any external library import. -/
structure CertificateEquiv (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a : A, invFun (toFun a) = a
  right_inv : ∀ b : B, toFun (invFun b) = b

/-- Forget the trajectory/history and keep only the terminal static certificate. -/
def forgetTrajectory {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v} :
    StaticWithTrajectoryCertificate le hRefl Time →
      StaticZornCertificate le hRefl :=
  fun C => C.static

/-- The static projection of a dynamic certificate. -/
def terminalProjection {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : DynamicZornCertificate le hRefl Time) :
    StaticZornCertificate le hRefl :=
  ⟨C.terminal, C.localClosure⟩

/-- The trajectory projection of a dynamic certificate. -/
def trajectoryProjection {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : DynamicZornCertificate le hRefl Time) :
    ExtensionTrajectory le Time :=
  C.trajectory

/-- Bundle the two projections of a dynamic certificate. -/
def staticWithTrajectoryProjection {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : DynamicZornCertificate le hRefl Time) :
    StaticWithTrajectoryCertificate le hRefl Time :=
  ⟨terminalProjection C, trajectoryProjection C, C.boundedByTerminal⟩

/-- Rebuild the dynamic certificate from static closure plus compatible trajectory. -/
def dynamicOfStaticWithTrajectory {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : StaticWithTrajectoryCertificate le hRefl Time) :
    DynamicZornCertificate le hRefl Time :=
  ⟨C.static.terminal, C.static.localClosure,
    C.trajectory, C.boundedByTerminal⟩

/--
The dynamic certificate preserves exactly its terminal closure and compatible
trajectory data.
-/
def dynamicCertificateEquivStaticWithTrajectory
    {P : Type u} (le : P → P → Prop)
    (hRefl : ∀ p : P, le p p) (Time : Type v) :
    CertificateEquiv (DynamicZornCertificate le hRefl Time)
      (StaticWithTrajectoryCertificate le hRefl Time) where
  toFun := staticWithTrajectoryProjection
  invFun := dynamicOfStaticWithTrajectory
  left_inv := by
    intro C
    cases C
    rfl
  right_inv := by
    intro C
    cases C
    rfl

/-- Rebuilding from the two projections returns the original dynamic certificate. -/
theorem dynamicCertificate_reconstructed_from_projections
    {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : DynamicZornCertificate le hRefl Time) :
    dynamicOfStaticWithTrajectory (staticWithTrajectoryProjection C) = C := by
  cases C
  rfl

/-- The trajectory projection recovers the exact stored trajectory. -/
theorem trajectoryProjection_preserves_trajectory
    {P : Type u} {le : P → P → Prop}
    {hRefl : ∀ p : P, le p p} {Time : Type v}
    (C : DynamicZornCertificate le hRefl Time) :
    trajectoryProjection C = C.trajectory := by
  rfl

/-!
## A finite witness that terminal-only forgetting loses information
-/

/-- A two-point poset-shaped carrier for the loss-of-history example. -/
inductive TinyPoint
  | low
  | high
deriving DecidableEq

/-- The order has `low <= high`, with `high` terminal. -/
def tinyLe : TinyPoint → TinyPoint → Prop
  | TinyPoint.low, _ => True
  | TinyPoint.high, TinyPoint.high => True
  | TinyPoint.high, TinyPoint.low => False

/-- Reflexivity for the tiny relation. -/
theorem tinyLe_refl : ∀ p : TinyPoint, tinyLe p p := by
  intro p
  cases p <;> trivial

/-- `high` is locally R1/R2 closed. -/
theorem tinyHigh_localClosure :
    LocalR1R2Closed tinyLe tinyLe_refl TinyPoint.high := by
  intro x
  constructor
  · exact observationalIdentity_base_extension tinyLe_refl TinyPoint.high x
  · cases x with
    | mk q hq =>
        cases q
        · cases hq
        · rfl

/-- The shared static terminal certificate for the tiny example. -/
def tinyStatic : StaticZornCertificate tinyLe tinyLe_refl :=
  ⟨TinyPoint.high, tinyHigh_localClosure⟩

/-- First trajectory: constantly at `high`. -/
def tinyTrajectoryA : ExtensionTrajectory tinyLe Bool where
  TimeLe := fun _ _ => False
  state := fun _ => TinyPoint.high
  monotone := by
    intro t u h
    cases h

/-- Second trajectory: it remembers a `low` point at `false` and `high` at `true`. -/
def tinyTrajectoryB : ExtensionTrajectory tinyLe Bool where
  TimeLe := fun _ _ => False
  state
    | false => TinyPoint.low
    | true => TinyPoint.high
  monotone := by
    intro t u h
    cases h

/-- The first trajectory is bounded by `high`. -/
theorem tinyTrajectoryA_bounded :
    BoundedByTerminal tinyLe TinyPoint.high tinyTrajectoryA := by
  intro t
  cases t <;> trivial

/-- The second trajectory is bounded by `high`. -/
theorem tinyTrajectoryB_bounded :
    BoundedByTerminal tinyLe TinyPoint.high tinyTrajectoryB := by
  intro t
  cases t <;> trivial

/-- First static-plus-trajectory certificate. -/
def tinyStaticWithTrajectoryA :
    StaticWithTrajectoryCertificate tinyLe tinyLe_refl Bool :=
  ⟨tinyStatic, tinyTrajectoryA, tinyTrajectoryA_bounded⟩

/-- Second static-plus-trajectory certificate with the same terminal. -/
def tinyStaticWithTrajectoryB :
    StaticWithTrajectoryCertificate tinyLe tinyLe_refl Bool :=
  ⟨tinyStatic, tinyTrajectoryB, tinyTrajectoryB_bounded⟩

/-- The two tiny trajectories differ. -/
theorem tinyTrajectoryA_ne_B :
    tinyTrajectoryA ≠ tinyTrajectoryB := by
  intro h
  have hState :
      tinyTrajectoryA.state false = tinyTrajectoryB.state false := by
    rw [h]
  cases hState

/-- The two static-plus-trajectory certificates differ. -/
theorem tinyStaticWithTrajectoryA_ne_B :
    tinyStaticWithTrajectoryA ≠ tinyStaticWithTrajectoryB := by
  intro h
  exact tinyTrajectoryA_ne_B (congrArg (fun C => C.trajectory) h)

/-- Forgetting the trajectory sends both certificates to the same static point. -/
theorem forgetTrajectory_tiny_A_eq_B :
    forgetTrajectory tinyStaticWithTrajectoryA =
      forgetTrajectory tinyStaticWithTrajectoryB := by
  rfl

/-- The terminal-only projection loses trajectory information. -/
theorem forgetTrajectory_not_injective_tiny :
    ¬ Function.Injective
      (forgetTrajectory
        (P := TinyPoint) (le := tinyLe) (hRefl := tinyLe_refl)
        : StaticWithTrajectoryCertificate tinyLe tinyLe_refl Bool →
            StaticZornCertificate tinyLe tinyLe_refl) := by
  intro hInjective
  exact tinyStaticWithTrajectoryA_ne_B
    (hInjective forgetTrajectory_tiny_A_eq_B)

end ZornR1R2
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.ZornR1R2.IsChain
#print axioms LocalSemanticClosure.ZornR1R2.UpperBound
#print axioms LocalSemanticClosure.ZornR1R2.Maximal
#print axioms LocalSemanticClosure.ZornR1R2.ZornPrinciple
#print axioms LocalSemanticClosure.ZornR1R2.ExtensionCarrier
#print axioms LocalSemanticClosure.ZornR1R2.LocalR1R2Closed
#print axioms LocalSemanticClosure.ZornR1R2.observationalIdentity_base_extension
#print axioms LocalSemanticClosure.ZornR1R2.observationalIdentity_extension_base
#print axioms LocalSemanticClosure.ZornR1R2.localR1R2Closed_iff_maximal
#print axioms LocalSemanticClosure.ZornR1R2.existsMaximal_iff_existsLocalR1R2Closed
#print axioms LocalSemanticClosure.ZornR1R2.zorn_as_r1r2_closure
#print axioms LocalSemanticClosure.ZornR1R2.residualNonempty_iff_strictLocalExtension
#print axioms LocalSemanticClosure.ZornR1R2.ExtensionTrajectory
#print axioms LocalSemanticClosure.ZornR1R2.StaticZornCertificate
#print axioms LocalSemanticClosure.ZornR1R2.DynamicZornCertificate
#print axioms LocalSemanticClosure.ZornR1R2.StaticWithTrajectoryCertificate
#print axioms LocalSemanticClosure.ZornR1R2.dynamicCertificateEquivStaticWithTrajectory
#print axioms LocalSemanticClosure.ZornR1R2.dynamicCertificate_reconstructed_from_projections
#print axioms LocalSemanticClosure.ZornR1R2.trajectoryProjection_preserves_trajectory
#print axioms LocalSemanticClosure.ZornR1R2.forgetTrajectory_not_injective_tiny
/- AXIOM_AUDIT_END -/
