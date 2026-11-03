module

public import Tournament.Probability.FiniteKernel
public import Tournament.Upper.CutProbabilities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Tournament

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

structure HoldingFamily (ι : Type*) [Fintype ι] where
  sampling : ProbabilityVector ι
  refresh : ProbabilityVector ι
  sampling_pos : ∀ i, 0 < sampling i
  refresh_pos : ∀ i, 0 < refresh i
  refresh_ge_half : ∀ i, sampling i / 2 ≤ refresh i

namespace HoldingFamily

noncomputable section

def ratio (H : HoldingFamily ι) (i : ι) : ℝ := H.refresh i / H.sampling i

def refreshRate (H : HoldingFamily ι) (τ : ℝ) (i : ι) : ℝ :=
  Upper.holdingFraction (τ * H.ratio i)

def meanRefreshRate (H : HoldingFamily ι) (τ : ℝ) : ℝ :=
  ∑ i, H.sampling i * H.refreshRate τ i

def destinationNormalizer (H : HoldingFamily ι) (τ : ℝ) : ℝ :=
  ∑ i, H.refresh i / (1 + τ * H.ratio i)

def maxRatio (H : HoldingFamily ι) : ℝ := by
  have : Nonempty ι := H.sampling.nonempty
  exact Finset.univ.sup' Finset.univ_nonempty H.ratio

theorem ratio_pos (H : HoldingFamily ι) (i : ι) : 0 < H.ratio i := by
  exact div_pos (H.refresh_pos i) (H.sampling_pos i)

theorem ratio_ge_half (H : HoldingFamily ι) (i : ι) : 1 / 2 ≤ H.ratio i := by
  apply (le_div_iff₀ (H.sampling_pos i)).mpr
  nlinarith [H.refresh_ge_half i]

theorem ratio_le_maxRatio (H : HoldingFamily ι) (i : ι) : H.ratio i ≤ H.maxRatio := by
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem weighted_ratio (H : HoldingFamily ι) (i : ι) :
    H.sampling i * H.ratio i = H.refresh i := by
  unfold ratio
  field_simp [ne_of_gt (H.sampling_pos i)]

theorem mean_ratio (H : HoldingFamily ι) : H.sampling.mean H.ratio = 1 := by
  unfold ProbabilityVector.mean
  calc
    (∑ i, H.sampling i * H.ratio i) = ∑ i, H.refresh i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold ratio
      field_simp [ne_of_gt (H.sampling_pos i)]
    _ = 1 := H.refresh.sum_eq_one

theorem refreshRate_pos (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    0 < H.refreshRate τ i := by
  unfold refreshRate Upper.holdingFraction
  have hratio := H.ratio_pos i
  positivity

theorem refreshRate_le_half (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) (i : ι) :
    H.refreshRate τ i ≤ 1 / 2 := by
  exact Upper.holdingFraction_le_half (mul_nonneg hτ (le_of_lt (H.ratio_pos i)))

theorem meanRefreshRate_pos (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    0 < H.meanRefreshRate τ := by
  have : Nonempty ι := H.sampling.nonempty
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (H.sampling_pos i) (H.refreshRate_pos hτ i)
  · exact Finset.univ_nonempty

theorem meanRefreshRate_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) :
    H.meanRefreshRate τ ≤ τ / 2 := by
  calc
    H.meanRefreshRate τ ≤ ∑ i, H.sampling i * ((τ * H.ratio i) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Upper.holdingFraction_le_linear (mul_nonneg hτ (le_of_lt (H.ratio_pos i))))
        (H.sampling.nonneg i)
    _ = (τ / 2) * H.sampling.mean H.ratio := by
      unfold ProbabilityVector.mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = τ / 2 := by rw [H.mean_ratio, mul_one]

theorem destinationNormalizer_pos (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < H.destinationNormalizer τ := by
  have : Nonempty ι := H.sampling.nonempty
  apply Finset.sum_pos
  · intro i _
    exact div_pos (H.refresh_pos i)
      (by have hr := H.ratio_pos i; positivity)
  · exact Finset.univ_nonempty

theorem destinationNormalizer_le_one (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) :
    H.destinationNormalizer τ ≤ 1 := by
  calc
    H.destinationNormalizer τ ≤ ∑ i, H.refresh i := by
      apply Finset.sum_le_sum
      intro i _
      have hr := H.ratio_pos i
      apply (div_le_iff₀ (by positivity : 0 < 1 + τ * H.ratio i)).mpr
      nlinarith [mul_nonneg (H.refresh.nonneg i) (mul_nonneg hτ (le_of_lt hr))]
    _ = 1 := H.refresh.sum_eq_one

theorem weighted_refreshRate (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) (i : ι) :
    H.sampling i * H.refreshRate τ i =
      (τ / 2) * (H.refresh i / (1 + τ * H.ratio i)) := by
  have hr := H.ratio_pos i
  have hden : 1 + τ * H.ratio i ≠ 0 := ne_of_gt (by positivity)
  rw [← H.weighted_ratio i]
  unfold refreshRate Upper.holdingFraction
  field_simp

theorem meanRefreshRate_normalizer (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ) :
    H.meanRefreshRate τ = (τ / 2) * H.destinationNormalizer τ := by
  unfold meanRefreshRate destinationNormalizer
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ H.weighted_refreshRate hτ i)

theorem refreshRate_over_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.refreshRate τ i / H.meanRefreshRate τ =
      H.ratio i / ((1 + τ * H.ratio i) * H.destinationNormalizer τ) := by
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hr := H.ratio_pos i
  have hz := H.destinationNormalizer_pos hτ0
  have hden : 1 + τ * H.ratio i ≠ 0 := ne_of_gt (by positivity)
  rw [H.meanRefreshRate_normalizer hτ0]
  unfold refreshRate Upper.holdingFraction
  field_simp

theorem refreshRate_ge_third_mean (H : HoldingFamily ι) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (i : ι) :
    H.meanRefreshRate τ / 3 ≤ H.refreshRate τ i := by
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hr := H.ratio_pos i
  have hrhalf := H.ratio_ge_half i
  have hz := H.destinationNormalizer_pos hτ0
  have hz1 := H.destinationNormalizer_le_one hτ0
  have hden : 0 < 1 + τ * H.ratio i := by positivity
  have hr1 : (1:ℝ) / 3 ≤ 1 / (2 + τ) := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<3) (by linarith : 0 < 2 + τ)).mpr
    linarith
  have hr2 : 1 / (2 + τ) ≤ H.ratio i / (1 + τ * H.ratio i) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 2 + τ) hden).mpr
    nlinarith
  have hr3 : H.ratio i / (1 + τ * H.ratio i) ≤
      H.ratio i / ((1 + τ * H.ratio i) * H.destinationNormalizer τ) := by
    apply (div_le_div_iff₀ hden (mul_pos hden hz)).mpr
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt hden)) (sub_nonneg.mpr hz1)]
  have hfinal : (1:ℝ) / 3 ≤ H.refreshRate τ i / H.meanRefreshRate τ := by
    rw [H.refreshRate_over_mean hτ i]
    exact le_trans hr1 (le_trans hr2 hr3)
  have hmul := (le_div_iff₀ (H.meanRefreshRate_pos hτ)).mp hfinal
  linarith

def destination (H : HoldingFamily ι) (τ : ℝ) (hτ : 0 < τ) : ProbabilityVector ι where
  weight i := (H.sampling i * H.refreshRate τ i) / H.meanRefreshRate τ
  nonneg i := div_nonneg
    (mul_nonneg (H.sampling.nonneg i) (le_of_lt (H.refreshRate_pos hτ i)))
    (le_of_lt (H.meanRefreshRate_pos hτ))
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (H.meanRefreshRate_pos hτ))

def kernel [DecidableEq ι] (H : HoldingFamily ι) (τ : ℝ) (hτ : 0 < τ) : FiniteKernel ι where
  entry i j := (1 - H.refreshRate τ i) * (if i = j then 1 else 0) +
    H.refreshRate τ i * H.destination τ hτ j
  nonneg i j := by
    have ha0 := le_of_lt (H.refreshRate_pos hτ i)
    have ha1 := H.refreshRate_le_half (le_of_lt hτ) i
    have hr := (H.destination τ hτ).nonneg j
    split <;> simp only [mul_one, mul_zero, zero_add]
    · exact add_nonneg (by linarith) (mul_nonneg ha0 hr)
    · exact mul_nonneg ha0 hr
  row_sum i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [(H.destination τ hτ).sum_eq_one]

theorem kernel_reversible [DecidableEq ι] (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    (H.kernel τ hτ).Reversible H.sampling := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · change H.sampling i * ((1 - H.refreshRate τ i) * (if i=j then 1 else 0) +
        H.refreshRate τ i * ((H.sampling j * H.refreshRate τ j) / H.meanRefreshRate τ)) =
      H.sampling j * ((1 - H.refreshRate τ j) * (if j=i then 1 else 0) +
        H.refreshRate τ j * ((H.sampling i * H.refreshRate τ i) / H.meanRefreshRate τ))
    simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij), mul_zero, zero_add]
    ring

theorem kernel_stationary [DecidableEq ι] (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    (H.kernel τ hτ).Stationary H.sampling :=
  FiniteKernel.reversible_stationary _ _ (H.kernel_reversible hτ)

theorem kernel_holding_lower [DecidableEq ι] (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    1 - H.refreshRate τ i ≤ H.kernel τ hτ i i := by
  have ha0 := le_of_lt (H.refreshRate_pos hτ i)
  have hr := (H.destination τ hτ).nonneg i
  change 1 - H.refreshRate τ i ≤ (1 - H.refreshRate τ i) * (if i=i then 1 else 0) + _
  simp only [ite_true, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg ha0 hr)

theorem kernel_holding_ge_half [DecidableEq ι] (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    1 / 2 ≤ H.kernel τ hτ i i := by
  have ha := H.refreshRate_le_half (le_of_lt hτ) i
  have hh := H.kernel_holding_lower hτ i
  linarith

end
end HoldingFamily
end Tournament
