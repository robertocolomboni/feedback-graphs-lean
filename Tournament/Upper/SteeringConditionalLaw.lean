module

public import Tournament.Upper.IdealFeedbackLawMeasurable
public import Tournament.Upper.LiftedCompressedLaw

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model
open scoped Classical

noncomputable section

universe u
variable {ι : Type u} {A : Type*} [Fintype ι] [Nonempty ι]

theorem roundedFeedbackPolicy_metadataIndependent (S : SteeringParameters ι) :
    S.roundedFeedbackPolicy.MetadataIndependent := by
  intro p q n j coins
  rfl

theorem idealFeedbackPolicy_metadataIndependent (S : SteeringParameters ι) :
    S.idealFeedbackPolicy.MetadataIndependent := by
  intro p q n j coins
  rfl

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace A]

theorem rounded_compressedLaw_weight_measurable
    (S : SteeringParameters ι) (hRound : S.rounded = true)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (x : metadataHistory S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun a ↦ S.roundedFeedbackPolicy.compressedLaw S.tournament (loss a) n B x) := by
  exact rounded_execution_weight_measurable S hRound loss hLoss n B
    ((executionTraceEquiv (ι := ι) S.m n B).symm x)

theorem ideal_compressedLaw_weight_measurable
    (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (x : metadataHistory S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun a ↦ S.idealFeedbackPolicy.compressedLaw S.tournament (loss a) n B x) := by
  exact ideal_execution_weight_measurable S hIdeal loss hLoss n B
    ((executionTraceEquiv (ι := ι) S.m n B).symm x)

theorem rounded_compressedLaw_atom_measurable
    (S : SteeringParameters ι) (hRound : S.rounded = true) (n : ℕ → ℕ) (B : ℕ)
    (x : metadataHistory S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun loss ↦ S.roundedFeedbackPolicy.compressedLaw S.tournament loss n B x) :=
  rounded_compressedLaw_weight_measurable S hRound (fun loss ↦ loss)
    (fun t i ↦ (measurable_pi_apply i).comp (measurable_pi_apply t)) n B x

theorem ideal_compressedLaw_atom_measurable
    (S : SteeringParameters ι) (hIdeal : S.rounded = false) (n : ℕ → ℕ) (B : ℕ)
    (x : metadataHistory S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun loss ↦ S.idealFeedbackPolicy.compressedLaw S.tournament loss n B x) :=
  ideal_compressedLaw_weight_measurable S hIdeal (fun loss ↦ loss)
    (fun t i ↦ (measurable_pi_apply i).comp (measurable_pi_apply t)) n B x

theorem rounded_liftedCompressedLaw_atom_measurable
    (S : SteeringParameters ι) (hRound : S.rounded = true) (n : ℕ → ℕ) (B : ℕ)
    (x : SeedMetadata.{u} S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun loss ↦ S.roundedFeedbackPolicy.liftedCompressedLaw S.tournament loss n B x) :=
  rounded_compressedLaw_atom_measurable S hRound n B (x.1.down, x.2)

theorem ideal_liftedCompressedLaw_atom_measurable
    (S : SteeringParameters ι) (hIdeal : S.rounded = false) (n : ℕ → ℕ) (B : ℕ)
    (x : SeedMetadata.{u} S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :
    Measurable (fun loss ↦ S.idealFeedbackPolicy.liftedCompressedLaw S.tournament loss n B x) :=
  ideal_compressedLaw_atom_measurable S hIdeal n B (x.1.down, x.2)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem rounded_liftedCompressedLaw_completionLocal [LinearOrder ι]
    (S : SteeringParameters ι) (default : ι) (E : ι → ι → Prop)
    (hTournament : S.tournament = selectedEdge E) (n : ℕ → ℕ) (B : ℕ) :
    ConditionalFeedback.CompletionLocal
      (fun loss ↦ S.roundedFeedbackPolicy.liftedCompressedLaw S.tournament loss n B) E := by
  rw [hTournament]
  exact S.roundedFeedbackPolicy.liftedCompressedLaw_completionLocal
    S.roundedFeedbackPolicy_metadataIndependent default E n B

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem ideal_liftedCompressedLaw_completionLocal [LinearOrder ι]
    (S : SteeringParameters ι) (default : ι) (E : ι → ι → Prop)
    (hTournament : S.tournament = selectedEdge E) (n : ℕ → ℕ) (B : ℕ) :
    ConditionalFeedback.CompletionLocal
      (fun loss ↦ S.idealFeedbackPolicy.liftedCompressedLaw S.tournament loss n B) E := by
  rw [hTournament]
  exact S.idealFeedbackPolicy.liftedCompressedLaw_completionLocal
    S.idealFeedbackPolicy_metadataIndependent default E n B

end
end Tournament.Upper.SteeringParameters
