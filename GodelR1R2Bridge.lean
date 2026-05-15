import R1R2Notation

/-!
# Abstract Gödel-to-R1/R2 bridge and exact dimension-2 gap

This file does not formalize Gödel's incompleteness theorem.

Gödel-style undecidability, once supplied as local proof/truth data, becomes
R2-undecidability from R1.  Its local gap is quantified by a minimal mediator
of exact dimension `2`.

It proves the following exact R1/R2 statement.

Given local proof/truth data for a sentence `delta` such that `delta` and
`neg delta` have the same proof-status observation but opposite truth-status
targets, the file proves:

* R2 is undecidable from R1:

```lean
R2IndecidableForR1 (LocalProofTruthBridge.obs B)
  (LocalProofTruthBridge.sigma B) I_proof
```

* equivalently, the R1/R2 residual is nonempty:

```lean
ResidualNonempty_R2 (LocalProofTruthBridge.obs B)
  (LocalProofTruthBridge.sigma B) I_proof
```

* on the induced two-state carrier
  `GodelPairState.delta / GodelPairState.negDelta`, this gap has exact proper
  mediated R2 dimension `2`:

```lean
ExactProperMediatedR2Dimension
  (GodelPairState.obs B) (GodelPairState.sigma B) I_proof 2
```

and the end-to-end package contains:

```lean
ResidualNonempty_R2 (GodelPairState.obs B) (GodelPairState.sigma B) I_proof
∧ MediatedResidualEmpty (GodelPairState.obs B) (GodelPairState.sigma B)
    I_proof GodelPairState.M
∧ WitnessedIrreducibleMediator (GodelPairState.obs B) I_proof
    GodelPairState.M
∧ (∀ m : Nat,
    m < 2 →
      ¬ ExistsProperMediatedR2CertificateAtDim
        (GodelPairState.obs B) (GodelPairState.sigma B) I_proof m)
```

Thus the formal content is:

```text
same R1 proof-status identity
+ R2 truth-status fracture
=> R1/R2 residual
=> exact proper mediated gap dimension 2.
```

The proof uses the abstract bridge needed by the R1/R2 reading of
proof-theoretic undecidability:

* R1 reads a proof-status observation;
* R2 reads a truth-status target;
* a sentence `delta` and its negation have the same R1 proof-status
  observation;
* their R2 truth statuses differ.

The minimal bridge is local: it only needs the two proof-status observations
for `delta` and `neg delta`.  A stronger global bridge, where false proof
status is equivalent to unprovability for every sentence, is provided as a
corollary-producing wrapper.

Thus a proof-theoretically undecidable sentence gives an R1/R2 residual once
the local proof-status and truth-status separation data are supplied.

The file then restricts to the local two-state carrier:

```lean
GodelPairState.delta
GodelPairState.negDelta
```

On this carrier, the proof/truth gap has exact proper mediated R2 dimension
`2`: the two states are identified by the R1 proof-status observation,
separated by the R2 truth-status target, closed by a `Fin 2` mediator, and no
proper mediated certificate exists in dimension `0` or `1`.

In short:

```text
proof/truth undecidability
=> R1/R2 residual
=> exact proper mediated gap dimension 2.
```

No quotient, no `Classical`, no `propext`.
-/

namespace LocalSemanticClosure
namespace GodelR1R2Bridge

open Standalone.RegimesSelfContained
open R1R2Notation

universe u

/-- The single R1 reader: proof status in the background theory. -/
inductive ProofInterface
  | proofStatusReader
deriving DecidableEq

/-- The active proof-status interface. -/
def I_proof : Subfamily ProofInterface
  | ProofInterface.proofStatusReader => True

/--
Local data for transporting proof-theoretic undecidability into R1/R2.

The structure does not require a global decision procedure for unprovability.
It only stores the local fact that `delta` and `neg delta` receive the same
R1 proof-status observation, plus the proof-theoretic non-provability facts
that justify reading the pair as a Gödel-style undecidable pair.
-/
structure LocalProofTruthBridge where
  Sentence : Type u
  neg : Sentence → Sentence
  provable : Sentence → Prop
  proofStatus : Sentence → Bool
  truthStatus : Sentence → Bool
  delta : Sentence
  not_provable_delta : ¬ provable delta
  not_provable_neg_delta : ¬ provable (neg delta)
  proofStatus_delta_false : proofStatus delta = false
  proofStatus_neg_delta_false : proofStatus (neg delta) = false
  truth_delta : truthStatus delta = true
  truth_neg_delta : truthStatus (neg delta) = false

namespace LocalProofTruthBridge

/-- R1 observation: proof status only. -/
def obs (B : LocalProofTruthBridge.{u}) :
    ProofInterface → B.Sentence → Bool
  | ProofInterface.proofStatusReader, s => B.proofStatus s

/-- R2 target: truth status. -/
def sigma (B : LocalProofTruthBridge.{u}) : B.Sentence → Bool :=
  B.truthStatus

/-- The distinguished sentence and its negation have the same R1 observation. -/
theorem delta_same_R1 (B : LocalProofTruthBridge.{u}) :
    B.delta ≡ᵢ[obs B, I_proof] B.neg B.delta := by
  intro j _hj
  cases j
  exact B.proofStatus_delta_false.trans B.proofStatus_neg_delta_false.symm

/-- The distinguished sentence and its negation are separated by R2 truth. -/
theorem delta_fractured_R2 (B : LocalProofTruthBridge.{u}) :
    R2Fracture (sigma B) B.delta (B.neg B.delta) := by
  intro hTruth
  unfold sigma at hTruth
  rw [B.truth_delta, B.truth_neg_delta] at hTruth
  cases hTruth

/--
Local proof-theoretic undecidability plus truth separation gives R2
undecidability from R1 in the local informational sense.
-/
theorem r2IndecidableForR1_of_localProofTheoreticIndecidable
    (B : LocalProofTruthBridge.{u}) :
    R2IndecidableForR1 (obs B) (sigma B) I_proof :=
  ⟨B.delta, B.neg B.delta,
    delta_fractured_R2 B,
    delta_same_R1 B⟩

/--
Equivalently, the same local data gives a nonempty R2 residual for the
proof-status R1 observation and the truth-status R2 target.
-/
theorem residualNonempty_of_localProofTheoreticIndecidable
    (B : LocalProofTruthBridge.{u}) :
    ResidualNonempty_R2 (obs B) (sigma B) I_proof :=
  (r2IndecidableForR1_iff_residualNonempty
    (obs B) (sigma B) I_proof).1
      (r2IndecidableForR1_of_localProofTheoreticIndecidable B)

end LocalProofTruthBridge

/-- The two-state carrier generated by a Gödel-style pair. -/
inductive GodelPairState
  | delta
  | negDelta
deriving DecidableEq

namespace GodelPairState

/-- Interpret the two-state carrier as the actual sentence pair supplied by `B`. -/
def sentenceOf (B : LocalProofTruthBridge.{u}) :
    GodelPairState → B.Sentence
  | delta => B.delta
  | negDelta => B.neg B.delta

/-- R1 observation on the two-state Gödel carrier: proof status only. -/
def obs (B : LocalProofTruthBridge.{u}) :
    ProofInterface → GodelPairState → Bool
  | ProofInterface.proofStatusReader, s =>
      B.proofStatus (sentenceOf B s)

/-- R2 target on the two-state Gödel carrier: truth status. -/
def sigma (B : LocalProofTruthBridge.{u}) :
    GodelPairState → Bool :=
  fun s => B.truthStatus (sentenceOf B s)

/-- The minimal mediator separating the Gödel pair. -/
def M : GodelPairState → Fin 2
  | delta => ⟨0, by decide⟩
  | negDelta => ⟨1, by decide⟩

/-- The two-state Gödel pair has the same R1 proof-status observation. -/
theorem jointSame_delta_negDelta (B : LocalProofTruthBridge.{u}) :
    JointSame (obs B) I_proof delta negDelta := by
  intro j _hj
  cases j
  exact B.proofStatus_delta_false.trans B.proofStatus_neg_delta_false.symm

/-- The two-state Gödel pair is separated by the R2 truth target. -/
theorem requiredDistinction_delta_negDelta
    (B : LocalProofTruthBridge.{u}) :
    RequiredDistinction (sigma B) delta negDelta := by
  intro hTruth
  unfold sigma sentenceOf at hTruth
  rw [B.truth_delta, B.truth_neg_delta] at hTruth
  cases hTruth

/-- The canonical Gödel pair gives a diagonal R1/R2 witness. -/
theorem diagonalizationWitness_delta_negDelta
    (B : LocalProofTruthBridge.{u}) :
    DiagonalizationWitness (obs B) (sigma B) I_proof delta negDelta :=
  ⟨requiredDistinction_delta_negDelta B,
    jointSame_delta_negDelta B⟩

/-- The two-state Gödel carrier has a nonempty R2 residual. -/
theorem residualNonempty_pair
    (B : LocalProofTruthBridge.{u}) :
    ResidualNonempty_R2 (obs B) (sigma B) I_proof :=
  ⟨delta, negDelta, diagonalizationWitness_delta_negDelta B⟩

/-- The minimal mediator separates the canonical Gödel pair. -/
theorem M_separates_delta_negDelta :
    M delta ≠ M negDelta := by
  decide

/-- The minimal mediator closes the two-state Gödel residual. -/
theorem mediatedResidualEmpty_M
    (B : LocalProofTruthBridge.{u}) :
    MediatedResidualEmpty (obs B) (sigma B) I_proof M := by
  intro x y hResidual
  cases x <;> cases y
  · exact hResidual.1 rfl
  · exact M_separates_delta_negDelta hResidual.2.2
  · exact M_separates_delta_negDelta hResidual.2.2.symm
  · exact hResidual.1 rfl

/--
The canonical Gödel pair remains indistinguishable for every subfamily of the
active proof-status interface.
-/
theorem jointSame_delta_negDelta_of_subset
    (B : LocalProofTruthBridge.{u})
    (K : Subfamily ProofInterface)
    (hSubset : Subfamily.Subset K I_proof) :
    JointSame (obs B) K delta negDelta := by
  intro j hj
  exact jointSame_delta_negDelta B j (hSubset j hj)

/-- The Gödel mediator has explicit non-descent witnesses for every proper subfamily. -/
theorem witnessedIrreducibleMediator_M
    (B : LocalProofTruthBridge.{u}) :
    WitnessedIrreducibleMediator (obs B) I_proof M := by
  intro K hProper
  exact
    ⟨delta,
      negDelta,
      jointSame_delta_negDelta_of_subset B K hProper.1,
      M_separates_delta_negDelta⟩

/-- The Gödel mediator is irreducible. -/
theorem irreducibleMediator_M
    (B : LocalProofTruthBridge.{u}) :
    IrreducibleMediator (obs B) I_proof M :=
  witnessedIrreducibleMediator_irreducibleMediator
    (obs B) I_proof M
    (witnessedIrreducibleMediator_M B)

/-- The two-state Gödel carrier gives a proper mediated R2 certificate. -/
theorem properMediatedR2Certificate_M
    (B : LocalProofTruthBridge.{u}) :
    ProperMediatedR2Certificate (obs B) (sigma B) I_proof M :=
  ⟨residualNonempty_pair B,
    mediatedResidualEmpty_M B,
    irreducibleMediator_M B⟩

/-- The two-state Gödel carrier gives a witnessed proper mediated R2 certificate. -/
theorem witnessedProperMediatedR2Certificate_M
    (B : LocalProofTruthBridge.{u}) :
    WitnessedProperMediatedR2Certificate (obs B) (sigma B) I_proof M :=
  ⟨residualNonempty_pair B,
    mediatedResidualEmpty_M B,
    witnessedIrreducibleMediator_M B⟩

/-- No smaller proper mediated R2 certificate exists for the two-state Gödel carrier. -/
theorem no_smaller_properMediatedR2Certificate
    (B : LocalProofTruthBridge.{u}) :
    ∀ m : Nat,
      m < 2 →
        ¬ ExistsProperMediatedR2CertificateAtDim
          (obs B) (sigma B) I_proof m := by
  intro m hm
  cases m with
  | zero =>
      exact no_properMediatedR2CertificateAtDim_zero
        (obs B) (sigma B) I_proof
  | succ m =>
      cases m with
      | zero =>
          exact no_properMediatedR2CertificateAtDim_one
            (obs B) (sigma B) I_proof
      | succ m =>
          have hLtOne : Nat.succ m < 1 :=
            Nat.lt_of_succ_lt_succ hm
          have hLtZero : m < 0 :=
            Nat.lt_of_succ_lt_succ hLtOne
          exact False.elim (Nat.not_lt_zero m hLtZero)

/-- The Gödel mediator realizes dimension-minimal proper R2 closure. -/
theorem dimensionMinimalProperMediatedR2Certificate_M
    (B : LocalProofTruthBridge.{u}) :
    DimensionMinimalProperMediatedR2Certificate
      (obs B) (sigma B) I_proof M :=
  ⟨properMediatedR2Certificate_M B,
    no_smaller_properMediatedR2Certificate B⟩

/-- The Gödel mediator realizes witnessed dimension-minimal proper R2 closure. -/
theorem dimensionMinimalWitnessedProperMediatedR2Certificate_M
    (B : LocalProofTruthBridge.{u}) :
    DimensionMinimalWitnessedProperMediatedR2Certificate
      (obs B) (sigma B) I_proof M :=
  ⟨witnessedProperMediatedR2Certificate_M B,
    no_smaller_properMediatedR2Certificate B⟩

/-- The exact proper mediated R2 dimension of the two-state Gödel carrier is `2`. -/
theorem exactProperMediatedR2Dimension_two
    (B : LocalProofTruthBridge.{u}) :
    ExactProperMediatedR2Dimension
      (obs B) (sigma B) I_proof 2 :=
  exactProperMediatedR2Dimension_of_dimensionMinimalProperCertificate
    (dimensionMinimalProperMediatedR2Certificate_M B)

/--
End-to-end extraction of the two-state Gödel R1/R2 package: residual
nonemptiness, mediated closure, witnessed irreducibility, and exclusion of
every smaller proper mediated dimension.
-/
theorem endToEnd_godelPair
    (B : LocalProofTruthBridge.{u}) :
    ResidualNonempty_R2 (obs B) (sigma B) I_proof
      ∧ MediatedResidualEmpty (obs B) (sigma B) I_proof M
      ∧ WitnessedIrreducibleMediator (obs B) I_proof M
      ∧ (∀ m : Nat,
          m < 2 →
            ¬ ExistsProperMediatedR2CertificateAtDim
              (obs B) (sigma B) I_proof m) :=
  endToEnd_staticWitnessedProperMediatedR2Certificate
    (obs B) (sigma B) I_proof M
    (dimensionMinimalWitnessedProperMediatedR2Certificate_M B)

end GodelPairState

/--
Global data for the same bridge.

This wrapper is convenient when a development has an explicit Boolean proof
status whose `false` value is equivalent to unprovability for every sentence.
The actual R1/R2 bridge still factors through the local bridge above.
-/
structure ProofTruthBridge where
  Sentence : Type u
  neg : Sentence → Sentence
  provable : Sentence → Prop
  proofStatus : Sentence → Bool
  proofStatus_false_iff_unprovable :
    ∀ s : Sentence, proofStatus s = false ↔ ¬ provable s
  truthStatus : Sentence → Bool
  delta : Sentence
  not_provable_delta : ¬ provable delta
  not_provable_neg_delta : ¬ provable (neg delta)
  truth_delta : truthStatus delta = true
  truth_neg_delta : truthStatus (neg delta) = false

namespace ProofTruthBridge

/-- The global bridge induces the minimal local bridge. -/
def toLocal (B : ProofTruthBridge.{u}) : LocalProofTruthBridge.{u} :=
  { Sentence := B.Sentence
    neg := B.neg
    provable := B.provable
    proofStatus := B.proofStatus
    truthStatus := B.truthStatus
    delta := B.delta
    not_provable_delta := B.not_provable_delta
    not_provable_neg_delta := B.not_provable_neg_delta
    proofStatus_delta_false :=
      (B.proofStatus_false_iff_unprovable B.delta).2
        B.not_provable_delta
    proofStatus_neg_delta_false :=
      (B.proofStatus_false_iff_unprovable (B.neg B.delta)).2
        B.not_provable_neg_delta
    truth_delta := B.truth_delta
    truth_neg_delta := B.truth_neg_delta }

/-- R1 observation induced by the local bridge. -/
def obs (B : ProofTruthBridge.{u}) :
    ProofInterface → B.Sentence → Bool :=
  LocalProofTruthBridge.obs B.toLocal

/-- R2 target induced by the local bridge. -/
def sigma (B : ProofTruthBridge.{u}) : B.Sentence → Bool :=
  LocalProofTruthBridge.sigma B.toLocal

/-- The distinguished sentence and its negation have the same R1 observation. -/
theorem delta_same_R1 (B : ProofTruthBridge.{u}) :
    B.delta ≡ᵢ[obs B, I_proof] B.neg B.delta :=
  LocalProofTruthBridge.delta_same_R1 B.toLocal

/-- The distinguished sentence and its negation are separated by R2 truth. -/
theorem delta_fractured_R2 (B : ProofTruthBridge.{u}) :
    R2Fracture (sigma B) B.delta (B.neg B.delta) :=
  LocalProofTruthBridge.delta_fractured_R2 B.toLocal

/--
Global proof-status data gives R2 undecidability from R1 by first producing
the minimal local bridge.
-/
theorem r2IndecidableForR1_of_proofTheoreticIndecidable
    (B : ProofTruthBridge.{u}) :
    R2IndecidableForR1 (obs B) (sigma B) I_proof :=
  LocalProofTruthBridge.r2IndecidableForR1_of_localProofTheoreticIndecidable
    B.toLocal

/--
Equivalently, the global data gives a nonempty R2 residual by factoring
through the local bridge.
-/
theorem residualNonempty_of_proofTheoreticIndecidable
    (B : ProofTruthBridge.{u}) :
    ResidualNonempty_R2 (obs B) (sigma B) I_proof :=
  LocalProofTruthBridge.residualNonempty_of_localProofTheoreticIndecidable
    B.toLocal

end ProofTruthBridge

end GodelR1R2Bridge
end LocalSemanticClosure

/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofInterface
#print axioms LocalSemanticClosure.GodelR1R2Bridge.I_proof
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.obs
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.sigma
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.delta_same_R1
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.delta_fractured_R2
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.r2IndecidableForR1_of_localProofTheoreticIndecidable
#print axioms LocalSemanticClosure.GodelR1R2Bridge.LocalProofTruthBridge.residualNonempty_of_localProofTheoreticIndecidable
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.obs
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.sigma
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.diagonalizationWitness_delta_negDelta
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.residualNonempty_pair
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.mediatedResidualEmpty_M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.witnessedIrreducibleMediator_M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.properMediatedR2Certificate_M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.no_smaller_properMediatedR2Certificate
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.dimensionMinimalProperMediatedR2Certificate_M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.dimensionMinimalWitnessedProperMediatedR2Certificate_M
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.exactProperMediatedR2Dimension_two
#print axioms LocalSemanticClosure.GodelR1R2Bridge.GodelPairState.endToEnd_godelPair
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge.toLocal
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge.delta_same_R1
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge.delta_fractured_R2
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge.r2IndecidableForR1_of_proofTheoreticIndecidable
#print axioms LocalSemanticClosure.GodelR1R2Bridge.ProofTruthBridge.residualNonempty_of_proofTheoreticIndecidable
/- AXIOM_AUDIT_END -/
