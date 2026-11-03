module

public import Tournament.Probability.ExponentialMoment
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω : Type*} [Fintype Ω]

def probability (μ : ProbabilityVector Ω) (A : Ω → Prop) : ℝ :=
  μ.mean (fun ω ↦ if A ω then 1 else 0)

theorem probability_nonneg (μ : ProbabilityVector Ω) (A : Ω → Prop) : 0 ≤ μ.probability A := by
  apply μ.mean_nonneg
  intro ω
  split <;> norm_num

theorem probability_mono (μ : ProbabilityVector Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    μ.probability A ≤ μ.probability B := by
  apply μ.mean_mono
  intro ω
  by_cases hA : A ω
  · simp only [ite_eq_left hA, ite_eq_left (h ω hA), le_refl]
  · rw [ite_eq_right hA]
    split <;> norm_num

theorem exponential_markov_le (μ : ProbabilityVector Ω) (V : Ω → ℝ) (θ a : ℝ) (hθ : 0 ≤ θ) :
    μ.probability (fun ω ↦ a < V ω) ≤ Real.exp (-θ*a)*μ.mean (fun ω ↦ Real.exp (θ*V ω)) := by
  unfold probability
  rw [← mean_const_mul]
  apply μ.mean_mono
  intro ω
  by_cases hV : a < V ω
  · rw [ite_eq_left hV, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
  · rw [ite_eq_right hV]
    positivity

theorem exponential_tail_le (μ : ProbabilityVector Ω) (V : Ω → ℝ) (θ a C : ℝ) (hθ : 0 ≤ θ)
    (hmgf : μ.mean (fun ω ↦ Real.exp (θ*V ω)) ≤ Real.exp C) :
    μ.probability (fun ω ↦ a < V ω) ≤ Real.exp (C-θ*a) := by
  calc
    _ ≤ Real.exp (-θ*a)*μ.mean (fun ω ↦ Real.exp (θ*V ω)) := μ.exponential_markov_le V θ a hθ
    _ ≤ Real.exp (-θ*a)*Real.exp C := mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ProbabilityVector

namespace TailConstants

theorem log_half_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Real.log (δ/2) ≤ -1/2 := by
  calc
    _ ≤ δ/2-1 := Real.log_le_sub_one_of_pos (by positivity)
    _ ≤ -1/2 := by linarith

theorem log_two_div_eq {δ : ℝ} (hδ : 0 < δ) : Real.log (2/δ) = -Real.log (δ/2) := by
  have heq : 2/δ = (δ/2)⁻¹ := by field_simp
  rw [heq, Real.log_inv]

theorem threshold_ge_one {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 100*Real.log (2/δ) ≤ M) : 1 ≤ M := by
  rw [log_two_div_eq hδ] at hM
  have h := log_half_le hδ hδ1
  linarith

theorem estimator_tail_le_half {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 100*Real.log (2/δ) ≤ M) : Real.exp (1/32-M/8) ≤ δ/2 := by
  rw [log_two_div_eq hδ] at hM
  have hlog := log_half_le hδ hδ1
  calc
    _ ≤ Real.exp (Real.log (δ/2)) := Real.exp_le_exp.mpr (by linarith)
    _ = δ/2 := Real.exp_log (by positivity)

theorem score_tail_le {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 100*Real.log (2/δ) ≤ M) : 2*Real.exp (-(M-1)/16) ≤ δ := by
  rw [log_two_div_eq hδ] at hM
  have hlog := log_half_le hδ hδ1
  have hexp : Real.exp (-(M-1)/16) ≤ δ/2 := by
    calc
      _ ≤ Real.exp (Real.log (δ/2)) := Real.exp_le_exp.mpr (by linarith)
      _ = δ/2 := Real.exp_log (by positivity)
  linarith

end TailConstants
end
end Tournament
