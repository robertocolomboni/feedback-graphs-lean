module

public import Tournament.Upper.SteeringConditionalLaw
public import Tournament.Upper.CompressedRegret
public import Tournament.Upper.AdaptiveRegret
public import Tournament.Model.RegretDecidable

@[expose] public section

universe u v

namespace Tournament.Model.MeasurableGame.Strategy

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι : Type u} [MeasurableSpace ι]

def expectedSwitches (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) : ℝ :=
  letI := σ.seedSpace
  ∫ ω, (switchCount T (fun t ↦ deterministicAction σ.learner E loss t ω) : ℝ) ∂σ.law

end
end Tournament.Model.MeasurableGame.Strategy

namespace Tournament.Model.ConditionalFeedback

open MeasureTheory MeasurableGame
open scoped Classical

noncomputable section

variable {Meta ι : Type u} [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι]
variable [MeasurableSpace Meta] [MeasurableSpace ι]
variable [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι] {T : ℕ}

theorem strategyOfPositive_expectedSwitches_eq_mean
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (hT : 0 < T)
    (E : ι → ι → Prop) (hLocal : CompletionLocal μ E)
    (loss : ℕ → ι → ℝ) (default : ι) :
    (strategyOfPositive μ hμ hT default).expectedSwitches T E loss =
      (μ loss).mean (fun x ↦ (switchCount T (traceActions default x.2) : ℝ)) := by
  cases T with
  | zero => omega
  | succ T => exact expected_switches_eq_mean μ hμ E hLocal loss default

end
end Tournament.Model.ConditionalFeedback

namespace Tournament.Model.FeedbackEW

open MeasureTheory Upper MeasurableGame ConditionalFeedback
open scoped Classical

noncomputable section

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] {m : ℕ}

def privateStrategy (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (n : ℕ → ℕ) (B : ℕ)
    (hμ : ∀ x, Measurable (fun loss ↦ P.liftedCompressedLaw F loss n B x))
    (hT : 0 < prefixHorizon (fun b ↦ n b+1) B) (default : ι) : Strategy.{u,0} ι :=
  strategyOfPositive (fun loss ↦ P.liftedCompressedLaw F loss n B) hμ hT default

theorem privateStrategy_regret_eq_mean [LinearOrder ι]
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (F E : ι → ι → Prop)
    (hF : F = selectedEdge E) (n : ℕ → ℕ) (B : ℕ)
    (hμ : ∀ x, Measurable (fun loss ↦ P.liftedCompressedLaw F loss n B x))
    (hT : 0 < prefixHorizon (fun b ↦ n b+1) B) (default : ι) (loss : ℕ → ι → ℝ) :
    (P.privateStrategy F n B hμ hT default).regret
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (executionPath default n B x)) := by
  have hLocal : CompletionLocal (fun loss ↦ P.liftedCompressedLaw F loss n B) E := by
    rw [hF]
    exact P.liftedCompressedLaw_completionLocal hMeta default E n B
  have hreg := strategyOfPositive_regret_eq_mean
    (fun loss ↦ P.liftedCompressedLaw F loss n B) hμ hT E hLocal loss default
  change (P.privateStrategy F n B hμ hT default).regret _ E loss = _ at hreg
  refine hreg.trans ((P.liftedCompressedLaw_mean F loss n B _).trans
    ((P.compressedLaw_regret_mean default F loss n B).trans ?_))
  apply congrArg (((P.algorithm F n loss).execution B).mean)
  funext x
  exact pathRegret_decidableEq _ _ _ _ _

theorem privateStrategy_expectedSwitches_eq_mean [LinearOrder ι]
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (F E : ι → ι → Prop)
    (hF : F = selectedEdge E) (n : ℕ → ℕ) (B : ℕ)
    (hμ : ∀ x, Measurable (fun loss ↦ P.liftedCompressedLaw F loss n B x))
    (hT : 0 < prefixHorizon (fun b ↦ n b+1) B) (default : ι) (loss : ℕ → ι → ℝ) :
    (P.privateStrategy F n B hμ hT default).expectedSwitches
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x) : ℝ)) := by
  have hLocal : CompletionLocal (fun loss ↦ P.liftedCompressedLaw F loss n B) E := by
    rw [hF]
    exact P.liftedCompressedLaw_completionLocal hMeta default E n B
  have hswitch := strategyOfPositive_expectedSwitches_eq_mean
    (fun loss ↦ P.liftedCompressedLaw F loss n B) hμ hT E hLocal loss default
  change (P.privateStrategy F n B hμ hT default).expectedSwitches _ E loss = _ at hswitch
  refine hswitch.trans ((P.liftedCompressedLaw_mean F loss n B _).trans
    ((P.compressedLaw_switches_mean default F loss n B).trans ?_))
  apply congrArg (((P.algorithm F n loss).execution B).mean)
  funext x
  exact congrArg (fun k : ℕ ↦ (k : ℝ)) (switchCount_decidableEq _ _ _ _)

end
end Tournament.Model.FeedbackEW

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model MeasurableGame
open scoped Classical

noncomputable section

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def roundedPrivateStrategy (S : SteeringParameters ι) (hRound : S.rounded = true)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) : Strategy.{u,0} ι :=
  S.roundedFeedbackPolicy.privateStrategy S.tournament n B
    (S.rounded_liftedCompressedLaw_atom_measurable hRound n B) hT default

def idealPrivateStrategy (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) : Strategy.{u,0} ι :=
  S.idealFeedbackPolicy.privateStrategy S.tournament n B
    (S.ideal_liftedCompressedLaw_atom_measurable hIdeal n B) hT default

theorem roundedPrivateStrategy_regret_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (hRound : S.rounded = true)
    (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.roundedPrivateStrategy hRound n B hT default).regret
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((S.algorithm n loss hLoss).execution B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (S.actions n default B x)) := by
  have h := S.roundedFeedbackPolicy.privateStrategy_regret_eq_mean
    S.roundedFeedbackPolicy_metadataIndependent S.tournament E hTournament n B
    (S.rounded_liftedCompressedLaw_atom_measurable hRound n B) hT default loss
  rw [S.roundedFeedbackPolicy_algorithm_eq hRound n loss hLoss] at h
  exact h

theorem idealPrivateStrategy_regret_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.idealPrivateStrategy hIdeal n B hT default).regret
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((S.algorithm n loss hLoss).execution B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (S.actions n default B x)) := by
  have h := S.idealFeedbackPolicy.privateStrategy_regret_eq_mean
    S.idealFeedbackPolicy_metadataIndependent S.tournament E hTournament n B
    (S.ideal_liftedCompressedLaw_atom_measurable hIdeal n B) hT default loss
  rw [S.idealFeedbackPolicy_algorithm_eq hIdeal n loss hLoss] at h
  exact h

theorem roundedPrivateStrategy_expectedSwitches_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (hRound : S.rounded = true)
    (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.roundedPrivateStrategy hRound n B hT default).expectedSwitches
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((S.algorithm n loss hLoss).execution B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (S.actions n default B x) : ℝ)) := by
  have h := S.roundedFeedbackPolicy.privateStrategy_expectedSwitches_eq_mean
    S.roundedFeedbackPolicy_metadataIndependent S.tournament E hTournament n B
    (S.rounded_liftedCompressedLaw_atom_measurable hRound n B) hT default loss
  rw [S.roundedFeedbackPolicy_algorithm_eq hRound n loss hLoss] at h
  exact h

theorem idealPrivateStrategy_expectedSwitches_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (n : ℕ → ℕ) (B : ℕ) (hT : 0 < prefixHorizon (fun b ↦ n b+1) B)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.idealPrivateStrategy hIdeal n B hT default).expectedSwitches
      (prefixHorizon (fun b ↦ n b+1) B) E loss =
    ((S.algorithm n loss hLoss).execution B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (S.actions n default B x) : ℝ)) := by
  have h := S.idealFeedbackPolicy.privateStrategy_expectedSwitches_eq_mean
    S.idealFeedbackPolicy_metadataIndependent S.tournament E hTournament n B
    (S.ideal_liftedCompressedLaw_atom_measurable hIdeal n B) hT default loss
  rw [S.idealFeedbackPolicy_algorithm_eq hIdeal n loss hLoss] at h
  exact h

end
end Tournament.Upper.SteeringParameters
