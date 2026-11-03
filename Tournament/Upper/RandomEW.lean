module

public import Tournament.Upper.SmoothedWeights
public import Tournament.Probability.RandomWeights

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω)

theorem adapted_finsetSum {α : Type*} {m : MeasurableSpace Ω} (s : Finset α) (f : α → Ω → ℝ)
    (hf : ∀ a ∈ s, AEStronglyMeasurable[m] (f a) μ) :
    AEStronglyMeasurable[m] (fun ω ↦ ∑ a ∈ s, f a ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact aestronglyMeasurable_const
  | @insert a s ha ih =>
    have hs := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have h := (hf a (Finset.mem_insert_self _ _)).fun_add hs
    simpa only [Finset.sum_insert ha] using h

theorem exponentialUpdate_aestronglyMeasurable {m : MeasurableSpace Ω}
    (p : Ω → ProbabilityVector ι) (η : ℝ) (g : Ω → ι → ℝ)
    (hp : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ p ω i) μ)
    (hg : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ g ω i) μ) (i : ι) :
    AEStronglyMeasurable[m] (fun ω ↦ Model.exponentialUpdate (p ω) η (g ω) i) μ := by
  let : MeasurableSpace Ω := mΩ
  have hexp (j : ι) : AEStronglyMeasurable[m] (fun ω ↦ Real.exp (-η*g ω j)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable ((hg j).const_mul (-η))
  have hnum (j : ι) : AEStronglyMeasurable[m] (fun ω ↦ p ω j*Real.exp (-η*g ω j)) μ := (hp j).mul (hexp j)
  have hden : AEStronglyMeasurable[m] (fun ω ↦ (p ω).mean (fun j ↦ Real.exp (-η*g ω j))) μ := by
    change AEStronglyMeasurable[m] (fun ω ↦ ∑ j, p ω j*Real.exp (-η*g ω j)) μ
    exact adapted_finsetSum μ Finset.univ _ (fun j _ ↦ hnum j)
  exact (hnum i).div₀ hden

theorem trajectory_aestronglyMeasurable {m : MeasurableSpace Ω}
    (π₀ : ProbabilityVector ι) (η : ℝ) (g : ℕ → Ω → ι → ℝ) (n : ℕ)
    (hg : ∀ t, t<n → ∀ i, AEStronglyMeasurable[m] (fun ω ↦ g t ω i) μ) (i : ι) :
    AEStronglyMeasurable[m] (fun ω ↦ trajectory π₀ η (fun t ↦ g t ω) n i) μ := by
  let : MeasurableSpace Ω := mΩ
  induction n generalizing i with
  | zero =>
    change AEStronglyMeasurable[m] (fun _ : Ω ↦ π₀ i) μ
    exact aestronglyMeasurable_const
  | succ n ih =>
    exact exponentialUpdate_aestronglyMeasurable μ (fun ω ↦ trajectory π₀ η (fun t ↦ g t ω) n) η (g n)
      (fun j ↦ ih (fun t ht ↦ hg t (by omega)) j) (hg n (by omega)) i

def weights [Nonempty ι] (η : ℝ) (g : ℕ → Ω → ι → ℝ) (b : ℕ) (ω : Ω) : ProbabilityVector ι :=
  trajectory uniform η (fun t ↦ g t ω) b

theorem smooth_aestronglyMeasurable [Nonempty ι] {m : MeasurableSpace Ω}
    (p : Ω → ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (hp : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ p ω i) μ) (i : ι) :
    AEStronglyMeasurable[m] (fun ω ↦ smooth (p ω) ε hε hε1 i) μ := by
  exact ((hp i).const_mul (1-ε)).add aestronglyMeasurable_const

variable [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem estimate_norm_le (η : ℝ) (hη : 0<η) (g : Ω → ι → ℝ)
    (hg : ∀ᵐ ω ∂μ, η*‖g ω‖≤1) : ∀ᵐ ω ∂μ, ‖g ω‖≤1/η := by
  filter_upwards [hg] with ω hω
  exact (le_div_iff₀ hη).mpr (by nlinarith)

theorem estimate_integrable (η : ℝ) (hη : 0<η) (g : Ω → ι → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (fun ω ↦ g ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, η*‖g ω‖≤1) (i : ι) : Integrable (fun ω ↦ g ω i) μ := by
  apply (integrable_const (1/η:ℝ)).mono' (hg i)
  filter_upwards [estimate_norm_le μ η hη g hbound] with ω hω
  exact le_trans (norm_le_pi_norm (g ω) i) hω

theorem estimate_square_integrable (η : ℝ) (hη : 0<η) (g : Ω → ι → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (fun ω ↦ g ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, η*‖g ω‖≤1) (i : ι) : Integrable (fun ω ↦ (g ω i)^2) μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ (g ω i)^2) μ := by
    simpa only [pow_two] using (hg i).fun_mul (hg i)
  apply (integrable_const ((1/η:ℝ)^2)).mono' hmeas
  filter_upwards [estimate_norm_le μ η hη g hbound] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hi : |g ω i|≤1/η := by
    simpa only [Real.norm_eq_abs] using le_trans (norm_le_pi_norm (g ω) i) hω
  have hi₁ := (abs_le.mp hi).1
  have hi₂ := (abs_le.mp hi).2
  have hp := mul_nonneg (sub_nonneg.mpr hi₂) (show 0≤1/η+g ω i by linarith)
  nlinarith

theorem estimate_secondMoment_integrable (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable (fun ω ↦ p ω i) μ)
    (η : ℝ) (hη : 0<η) (g : Ω → ι → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (fun ω ↦ g ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, η*‖g ω‖≤1) : Integrable (fun ω ↦ (p ω).squareNorm (g ω)) μ :=
  MeasureRandomWeights.integrable_mean μ p hp (fun ω i ↦ (g ω i)^2)
    (estimate_square_integrable μ η hη g hg hbound)

end
end Tournament.Upper.ExponentialWeights
