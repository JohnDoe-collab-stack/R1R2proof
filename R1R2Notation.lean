import RegimesSelfContained

/-!
# R1/R2 notation as Lean propositions

This file gives a compact Lean layer for the identity notation used in
`Notation.md`.

Core informal notation:

```text
R1-identity:
  x ≡ᵢ y

R2-fracture:
  sigma(x) and sigma(y) are distinct

M-refined identity:
  x ≡ᵢ,ₘ y := x ≡ᵢ y and M(x) = M(y)
```

The notation is parameterized by the data that make it meaningful:

* `x ≡ᵢ[obs, I] y` means observational identity relative to `obs` and `I`;
* `x ≡ᵢ,ₘ[obs, I, M] y` means the mediated refinement of that identity.

No quotient is constructed here.  The file only fixes the propositions and
proves their exact expansion into the kernel definitions.
-/

namespace LocalSemanticClosure
namespace R1R2Notation

open Standalone.RegimesSelfContained

universe u v w z

/-- Observational identity relative to an active interface family. -/
abbrev ObservationalIdentity
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J) (x y : S) : Prop :=
  JointSame obs I x y

/-- The R2 target distinguishes two states. -/
abbrev R2Fracture
    {S : Type v} {Y : Type z}
    (sigma : S → Y) (x y : S) : Prop :=
  RequiredDistinction sigma x y

/-- Observational identity refined by a finite mediator coordinate. -/
abbrev MediatedIdentity
    {J : Type u} {S : Type v} {V : Type w} {n : Nat}
    (obs : J → S → V) (I : Subfamily J)
    (M : S → Fin n) (x y : S) : Prop :=
  MediatedSame obs I M x y

notation:50 x " ≡ᵢ[" obs ", " I "] " y =>
  ObservationalIdentity obs I x y

notation:50 x " ≡ᵢ,ₘ[" obs ", " I ", " M "] " y =>
  MediatedIdentity obs I M x y

/-- The notation `x ≡ᵢ[obs, I] y` is exactly `JointSame obs I x y`. -/
theorem observationalIdentity_iff_jointSame
    {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J) (x y : S) :
    (x ≡ᵢ[obs, I] y) ↔ JointSame obs I x y := by
  rfl

/-- The R2 fracture notation layer is exactly required distinction. -/
theorem r2Fracture_iff_requiredDistinction
    {S : Type v} {Y : Type z}
    (sigma : S → Y) (x y : S) :
    R2Fracture sigma x y ↔ RequiredDistinction sigma x y := by
  rfl

/--
The notation `x ≡ᵢ,ₘ[obs, I, M] y` is exactly observational identity plus
equality of the mediator coordinate.
-/
theorem mediatedIdentity_iff_observationalIdentity_and_mediator
    {J : Type u} {S : Type v} {V : Type w} {n : Nat}
    (obs : J → S → V) (I : Subfamily J)
    (M : S → Fin n) (x y : S) :
    (x ≡ᵢ,ₘ[obs, I, M] y) ↔
      (x ≡ᵢ[obs, I] y) ∧ M x = M y := by
  rfl

/--
A diagonal witness is exactly an R2 fracture together with R1 observational
identity.
-/
theorem diagonalizationWitness_iff_r2Fracture_and_observationalIdentity
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (x y : S) :
    DiagonalizationWitness obs sigma I x y ↔
      R2Fracture sigma x y ∧ (x ≡ᵢ[obs, I] y) := by
  rfl

/--
R2 is undecidable from R1, in the local informational sense, when one R1
identity class contains an R2 fracture.

This is the notation-level form of residual nonemptiness.  It is not a
proof-theoretic Gödel undecidability statement.
-/
abbrev R2IndecidableForR1
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) : Prop :=
  ∃ x y : S, R2Fracture sigma x y ∧ (x ≡ᵢ[obs, I] y)

/--
The local informational statement “R2 is undecidable from R1” is exactly
nonemptiness of the R2 residual.
-/
theorem r2IndecidableForR1_iff_residualNonempty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) :
    R2IndecidableForR1 obs sigma I ↔
      ResidualNonempty_R2 obs sigma I := by
  rfl

/--
A mediated residual is exactly an R2 fracture that remains after the mediated
identity refinement.
-/
theorem mediatedResidual_iff_r2Fracture_and_mediatedIdentity
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (M : S → Fin n) (x y : S) :
    MediatedResidual obs sigma I M x y ↔
      R2Fracture sigma x y ∧ (x ≡ᵢ,ₘ[obs, I, M] y) := by
  rfl

/--
If two states have mediated identity, then they have the underlying
observational identity.
-/
theorem observationalIdentity_of_mediatedIdentity
    {J : Type u} {S : Type v} {V : Type w} {n : Nat}
    {obs : J → S → V} {I : Subfamily J}
    {M : S → Fin n} {x y : S} :
    (x ≡ᵢ,ₘ[obs, I, M] y) → (x ≡ᵢ[obs, I] y) := by
  intro h
  exact h.1

/--
If a diagonal witness is not separated by the mediator, it is a mediated
residual.
-/
theorem mediatedResidual_of_diagonalizationWitness_and_mediator_same
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} {x y : S} :
    DiagonalizationWitness obs sigma I x y →
      M x = M y →
        MediatedResidual obs sigma I M x y := by
  intro hDiag hM
  exact ⟨hDiag.1, ⟨hDiag.2, hM⟩⟩

/--
Conversely, every mediated residual contains an underlying diagonal witness.
-/
theorem diagonalizationWitness_of_mediatedResidual
    {J : Type u} {S : Type v} {V : Type w} {Y : Type z} {n : Nat}
    {obs : J → S → V} {sigma : S → Y}
    {I : Subfamily J} {M : S → Fin n} {x y : S} :
    MediatedResidual obs sigma I M x y →
      DiagonalizationWitness obs sigma I x y := by
  intro hResidual
  exact ⟨hResidual.1, hResidual.2.1⟩

end R1R2Notation
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.R1R2Notation.ObservationalIdentity
#print axioms LocalSemanticClosure.R1R2Notation.R2Fracture
#print axioms LocalSemanticClosure.R1R2Notation.MediatedIdentity
#print axioms LocalSemanticClosure.R1R2Notation.observationalIdentity_iff_jointSame
#print axioms LocalSemanticClosure.R1R2Notation.mediatedIdentity_iff_observationalIdentity_and_mediator
#print axioms LocalSemanticClosure.R1R2Notation.diagonalizationWitness_iff_r2Fracture_and_observationalIdentity
#print axioms LocalSemanticClosure.R1R2Notation.R2IndecidableForR1
#print axioms LocalSemanticClosure.R1R2Notation.r2IndecidableForR1_iff_residualNonempty
#print axioms LocalSemanticClosure.R1R2Notation.mediatedResidual_iff_r2Fracture_and_mediatedIdentity
#print axioms LocalSemanticClosure.R1R2Notation.mediatedResidual_of_diagonalizationWitness_and_mediator_same
#print axioms LocalSemanticClosure.R1R2Notation.diagonalizationWitness_of_mediatedResidual
/- AXIOM_AUDIT_END -/
