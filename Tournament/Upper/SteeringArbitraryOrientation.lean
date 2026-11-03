module

public import Tournament.Model.ObservableOrientation
public import Tournament.Model.ConditionalFeedbackRegret
public import Tournament.Upper.SteeringMinimax
public import Tournament.Upper.GraphTunedExecution
public import Tournament.Upper.TrivialRegimes

@[expose] public section

universe u

namespace Tournament.Model.FeedbackEW

open MeasureTheory Upper MeasurableGame ConditionalFeedback
open scoped Classical
noncomputable section

variable {ι : Type u} [Fintype ι] [Nonempty ι] {m : ℕ}

theorem liftedCompressedLaw_completionLocal_of_observed
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (default : ι)
    (F E : ι → ι → Prop) (hObs : OrientationObserved E F) (n : ℕ → ℕ) (B : ℕ) :
    CompletionLocal (fun loss ↦ P.liftedCompressedLaw F loss n B) E := by
  intro loss t ht q a i
  rw [prefixMass_liftedCompressedLaw,prefixMass_liftedCompressedLaw]
  apply P.compressed_prefixMass_eq_of_observations hMeta default F
  intro s hs
  let j : Fin t := ⟨s.val,by omega⟩
  have hsnoc : (Fin.snoc a i : Fin (t+1) → ι) s=a j := by
    have hs' : s=j.castSucc := Fin.ext rfl
    rw [hs',Fin.snoc_castSucc]
  rw [hsnoc]
  exact observedCompletion_preserves_comparison_of_observed E F hObs a loss j

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem privateStrategy_regret_eq_mean_of_observed
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (F E : ι → ι → Prop)
    (hObs : OrientationObserved E F) (n : ℕ → ℕ) (B : ℕ)
    (hμ : ∀ x, Measurable (fun loss ↦ P.liftedCompressedLaw F loss n B x))
    (hT : 0<prefixHorizon (fun b ↦ n b+1) B) (default : ι) (loss : ℕ → ι → ℝ) :
    (P.privateStrategy F n B hμ hT default).regret
      (prefixHorizon (fun b ↦ n b+1) B) E loss=
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (executionPath default n B x)) := by
  have hLocal := P.liftedCompressedLaw_completionLocal_of_observed hMeta default F E hObs n B
  have hreg := strategyOfPositive_regret_eq_mean
    (fun loss ↦ P.liftedCompressedLaw F loss n B) hμ hT E hLocal loss default
  change (P.privateStrategy F n B hμ hT default).regret _ E loss=_ at hreg
  refine hreg.trans ((P.liftedCompressedLaw_mean F loss n B _).trans
    ((P.compressedLaw_regret_mean default F loss n B).trans ?_))
  apply congrArg (((P.algorithm F n loss).execution B).mean)
  funext x
  exact pathRegret_decidableEq _ _ _ _ _

theorem privateStrategy_expectedSwitches_eq_mean_of_observed
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (F E : ι → ι → Prop)
    (hObs : OrientationObserved E F) (n : ℕ → ℕ) (B : ℕ)
    (hμ : ∀ x, Measurable (fun loss ↦ P.liftedCompressedLaw F loss n B x))
    (hT : 0<prefixHorizon (fun b ↦ n b+1) B) (default : ι) (loss : ℕ → ι → ℝ) :
    (P.privateStrategy F n B hμ hT default).expectedSwitches
      (prefixHorizon (fun b ↦ n b+1) B) E loss=
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x) : ℝ)) := by
  have hLocal := P.liftedCompressedLaw_completionLocal_of_observed hMeta default F E hObs n B
  have hswitch := strategyOfPositive_expectedSwitches_eq_mean
    (fun loss ↦ P.liftedCompressedLaw F loss n B) hμ hT E hLocal loss default
  change (P.privateStrategy F n B hμ hT default).expectedSwitches _ E loss=_ at hswitch
  refine hswitch.trans ((P.liftedCompressedLaw_mean F loss n B _).trans
    ((P.compressedLaw_switches_mean default F loss n B).trans ?_))
  apply congrArg (((P.algorithm F n loss).execution B).mean)
  funext x
  exact congrArg (fun k : ℕ ↦ (k:ℝ)) (switchCount_decidableEq _ _ _ _)

end
end Tournament.Model.FeedbackEW
