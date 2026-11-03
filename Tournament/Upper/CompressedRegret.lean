module

public import Tournament.Upper.CompressedPrefixLocality
public import Tournament.Model.ConditionalFeedbackRegret

@[expose] public section

namespace Tournament.Model.FeedbackEW

open scoped BigOperators Classical
open Upper ConditionalFeedback

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] {m : ℕ}

omit [Fintype ι] [Nonempty ι] in
theorem compressed_traceActions (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n B) (t : ℕ) (ht : t < prefixHorizon (fun b ↦ n b+1) B) :
    traceActions default (executionTraceEquiv (ι := ι) m n B x).2 t =
      executionPath default n B x t := by
  rw [traceActions_of_lt default _ t ht]
  exact executionTrace_eq_actions default m n B x ⟨t,ht⟩

theorem compressed_pathRegret (default : ι) (loss : ℕ → ι → ℝ)
    (n : ℕ → ℕ) (B : ℕ) (x : ExecutionHistory ι m n B) :
    pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss
      (traceActions default (executionTraceEquiv (ι := ι) m n B x).2) =
    pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (executionPath default n B x) := by
  apply pathRegret_eq_of_action_prefix
  exact compressed_traceActions default n B x

omit [Fintype ι] [Nonempty ι] in
theorem compressed_switchCount (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n B) :
    switchCount (prefixHorizon (fun b ↦ n b+1) B)
      (traceActions default (executionTraceEquiv (ι := ι) m n B x).2) =
    switchCount (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x) := by
  apply switchCount_eq_of_prefix
  exact compressed_traceActions default n B x

theorem compressedLaw_regret_mean (P : FeedbackEW ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ) :
    (P.compressedLaw F loss n B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (traceActions default x.2)) =
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (executionPath default n B x)) := by
  rw [compressedLaw, ProbabilityVector.reindex_mean]
  simp only [compressed_pathRegret]

theorem compressedLaw_switches_mean (P : FeedbackEW ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ) :
    (P.compressedLaw F loss n B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (traceActions default x.2) : ℝ)) =
    ((P.algorithm F n loss).execution B).mean (fun x ↦
      (switchCount (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x) : ℝ)) := by
  rw [compressedLaw, ProbabilityVector.reindex_mean]
  simp only [compressed_switchCount]

end
end Tournament.Model.FeedbackEW
