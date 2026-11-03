module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Upper

noncomputable section

def holdingFraction (z : ℝ) : ℝ := z / (2 * (1 + z))

def cutProbability (τ α : ℝ) : ℝ := τ + (1 - τ) * holdingFraction (τ * α)

def energyWeight (τ α : ℝ) : ℝ := τ * α / (2 + τ * α)

def spectralCorrelation (τ α : ℝ) : ℝ :=
  (1 - τ) * ((2 + τ * α) / (2 * (1 + τ * α)))

theorem holdingFraction_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ holdingFraction z := by
  unfold holdingFraction
  positivity

theorem holdingFraction_le_half {z : ℝ} (hz : 0 ≤ z) :
    holdingFraction z ≤ 1 / 2 := by
  unfold holdingFraction
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + z))).mpr
  linarith

theorem holdingFraction_le_linear {z : ℝ} (hz : 0 ≤ z) :
    holdingFraction z ≤ z / 2 := by
  unfold holdingFraction
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + z)) (by norm_num : (0:ℝ)<2)).mpr
  nlinarith [sq_nonneg z]

theorem holdingFraction_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    holdingFraction a ≤ holdingFraction b := by
  have hb : 0 ≤ b := le_trans ha hab
  unfold holdingFraction
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + a))
    (by positivity : 0 < 2 * (1 + b))).mpr
  nlinarith

theorem holdingFraction_double {z : ℝ} (hz : 0 ≤ z) :
    holdingFraction (2 * z) ≤ 2 * holdingFraction z := by
  have heq : 2 * holdingFraction z = z / (1 + z) := by
    unfold holdingFraction
    field_simp
  rw [heq]
  unfold holdingFraction
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + 2 * z))
    (by positivity : 0 < 1 + z)).mpr
  nlinarith [sq_nonneg z]

theorem one_sub_correlation {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    1 - spectralCorrelation τ α = cutProbability τ α := by
  have hden : 2 * (1 + τ * α) ≠ 0 := ne_of_gt (by positivity)
  unfold spectralCorrelation cutProbability holdingFraction
  field_simp
  ring

theorem cutProbability_mono {τ a b : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    cutProbability τ a ≤ cutProbability τ b := by
  unfold cutProbability
  have hm := mul_le_mul_of_nonneg_left
    (holdingFraction_mono (mul_nonneg hτ ha) (mul_le_mul_of_nonneg_left hab hτ))
    (sub_nonneg.mpr hτ1)
  exact add_le_add (le_refl τ) hm

theorem rate_le_cutProbability {τ α : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 0 ≤ α) : τ ≤ cutProbability τ α := by
  unfold cutProbability
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr hτ1) (holdingFraction_nonneg (mul_nonneg hτ hα)))

theorem holdingFraction_le_cutProbability {τ α : ℝ} (hτ : 0 ≤ τ)
    (hα : 0 ≤ α) : holdingFraction (τ * α) ≤ cutProbability τ α := by
  have hu : holdingFraction (τ * α) ≤ 1 :=
    le_trans (holdingFraction_le_half (mul_nonneg hτ hα)) (by norm_num)
  unfold cutProbability
  nlinarith [mul_nonneg hτ (sub_nonneg.mpr hu)]

theorem cutProbability_le_one {τ α : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 0 ≤ α) : cutProbability τ α ≤ 1 := by
  have hu : holdingFraction (τ * α) ≤ 1 :=
    le_trans (holdingFraction_le_half (mul_nonneg hτ hα)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hτ1)
  unfold cutProbability
  linarith

theorem cutProbability_double {τ α : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 0 ≤ α) : cutProbability τ (2 * α) ≤ 2 * cutProbability τ α := by
  have hz := mul_nonneg hτ hα
  have hdouble := holdingFraction_double hz
  have hm := mul_le_mul_of_nonneg_left hdouble (sub_nonneg.mpr hτ1)
  unfold cutProbability
  rw [show τ * (2 * α) = 2 * (τ * α) by ring]
  nlinarith

theorem cutProbability_le_rate_add {τ α : ℝ} (hτ : 0 ≤ τ) (_hτ1 : τ ≤ 1)
    (hα : 0 ≤ α) : cutProbability τ α ≤ τ + (τ * α) / 2 := by
  have hz := mul_nonneg hτ hα
  have hu0 := holdingFraction_nonneg hz
  have hu := holdingFraction_le_linear hz
  have hm : (1 - τ) * holdingFraction (τ * α) ≤ holdingFraction (τ * α) := by
    nlinarith [mul_nonneg hτ hu0]
  unfold cutProbability
  linarith

theorem cutProbability_div_eight_le_energyWeight {τ α : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hα : 1 / 2 ≤ α) :
    cutProbability τ α / 8 ≤ energyWeight τ α := by
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hα0 : 0 ≤ α := by linarith
  let z := τ * α
  have hz : 0 ≤ z := mul_nonneg hτ0 hα0
  have hτz : τ ≤ 2 * z := by
    dsimp [z]
    nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hα)]
  have hcut : cutProbability τ α ≤ (5 / 2) * z := by
    have h := cutProbability_le_rate_add hτ0 hτ1 hα0
    change cutProbability τ α ≤ τ + z / 2 at h
    linarith
  have hden : 0 < 2 + z := by linarith
  change cutProbability τ α / 8 ≤ z / (2 + z)
  by_cases hz1 : z ≤ 1
  · have hpsi : z / 3 ≤ z / (2 + z) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<3) hden).mpr
      nlinarith [mul_nonneg hz (sub_nonneg.mpr hz1)]
    linarith
  · have hz1' : 1 ≤ z := le_of_lt (lt_of_not_ge hz1)
    have hpsi : (1:ℝ) / 3 ≤ z / (2 + z) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<3) hden).mpr
      linarith
    have hcut1 := cutProbability_le_one hτ0 hτ1 hα0
    linarith

end
end Tournament.Upper
