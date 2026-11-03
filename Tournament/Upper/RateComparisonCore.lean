module

public import Tournament.Upper.WithinBand
public import Tournament.Probability.DyadicTail

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

def bandValue (b : ℕ) : ℝ := (2:ℝ)^b/2

theorem bandValue_pos (b : ℕ) : 0<bandValue b := by unfold bandValue; positivity

theorem bandValue_ge_half (b : ℕ) : 1/2≤bandValue b := by
  have hp : (1:ℝ)≤2^b := one_le_pow₀ (by norm_num)
  unfold bandValue
  linarith

theorem bandValue_dyadic_bound (m b : ℕ) (hb : b<m) :
    DyadicRate.base m*(2*bandValue b)≤1/2 := by
  have hpow : (2:ℝ)^(b+1)≤2^m := pow_le_pow_right₀ (by norm_num) (by omega)
  have hm := mul_le_mul_of_nonneg_left hpow (le_of_lt (DyadicRate.base_pos m))
  rw [DyadicRate.base_mul_pow,pow_succ] at hm
  unfold bandValue
  nlinarith

theorem dyadic_ratio_bound {κ τ a : ℝ} (hκ : 0<κ) (hκτ : κ≤τ)
    (ha : 0≤a) (hcap : κ*(2*a)≤1/2) :
    a≤(3/(2*κ))*cutProbability τ (2*a) := by
  have hτ : 0<τ := lt_of_lt_of_le hκ hκτ
  have hτ0 := le_of_lt hτ
  have hκ0 := le_of_lt hκ
  have hc0 : 0≤cutProbability τ (2*a) :=
    le_trans (holdingFraction_nonneg (by positivity)) (holdingFraction_le_cutProbability hτ0 (by positivity))
  have hh : τ*a≤cutProbability τ (2*a)*(1+τ*(2*a)) := by
    have hg := holdingFraction_le_cutProbability hτ0 (show 0≤2*a by positivity)
    unfold holdingFraction at hg
    have hd : 0<2*(1+τ*(2*a)) := by positivity
    have hm := (div_le_iff₀ hd).mp hg
    nlinarith
  have hv : κ*(1+τ*(2*a))≤(3/2)*τ := by
    have hm := mul_le_mul_of_nonneg_left hcap hτ0
    nlinarith
  have hhκ := mul_le_mul_of_nonneg_left hh hκ0
  have hvc := mul_le_mul_of_nonneg_right hv hc0
  have hcancel : τ*(κ*a)≤τ*((3/2)*cutProbability τ (2*a)) := by nlinarith
  have hmain := (mul_le_mul_iff_right₀ hτ).mp hcancel
  rw [show (3/(2*κ))*cutProbability τ (2*a)=3*cutProbability τ (2*a)/(2*κ) by ring]
  apply (le_div_iff₀ (show 0<2*κ by positivity)).mpr
  nlinarith

theorem cutProbability_matched_product {τ σ α β : ℝ} (hτ : 0≤τ) (hτσ : τ≤σ)
    (hα : 0≤α) (heq : σ*β=τ*α) :
    cutProbability τ α≤cutProbability σ β := by
  have hh := holdingFraction_le_half (mul_nonneg hτ hα)
  unfold cutProbability
  rw [heq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hτσ)
    (show 0≤1-holdingFraction (τ*α) by linarith)]

theorem rate_covariance_to_gain {κ τ σ a b : ℝ} (hκ : 0<κ)
    (hτ : 0<τ) (hτ1 : τ≤1) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκτ : κ≤τ) (ha : 0≤a) (hb : 0≤b) (hcap : κ*(2*a)≤1/2)
    (hcut : cutProbability τ (2*a)≤cutProbability σ b)
    (y : ℕ → ℝ) (offset h : ℕ) :
    a*GeometricPartition.quadratic (spectralCorrelation τ (2*a)) y offset h≤
      (3/κ)*(cutProbability σ b*GeometricPartition.quadratic (spectralCorrelation σ b) y offset h) := by
  have hχ := spectralCorrelation_bounds hτ hτ1 (show 0≤2*a by positivity)
  have hχ' := spectralCorrelation_bounds hσ hσ1 hb
  have hχle : spectralCorrelation σ b≤spectralCorrelation τ (2*a) := by
    have h1 := one_sub_correlation (le_of_lt hτ) (show 0≤2*a by positivity)
    have h2 := one_sub_correlation (le_of_lt hσ) hb
    linarith
  have hcomp := GeometricPartition.quadratic_comparison hχ'.1 hχle hχ.2 y offset h
  rw [one_sub_correlation (le_of_lt hσ) hb,one_sub_correlation (le_of_lt hτ) (show 0≤2*a by positivity)] at hcomp
  have hcpos : 0<cutProbability τ (2*a) :=
    lt_of_lt_of_le hτ (rate_le_cutProbability (le_of_lt hτ) hτ1 (by positivity))
  have hratio := dyadic_ratio_bound hκ hκτ ha hcap
  have hc' : 0≤cutProbability σ b :=
    le_trans (le_of_lt hσ) (rate_le_cutProbability (le_of_lt hσ) hσ1 hb)
  have hcoefficient : a*(2*cutProbability σ b/cutProbability τ (2*a))≤(3/κ)*cutProbability σ b := by
    rw [show a*(2*cutProbability σ b/cutProbability τ (2*a))=
      (a*(2*cutProbability σ b))/cutProbability τ (2*a) by ring]
    apply (div_le_iff₀ hcpos).mpr
    have hm := mul_le_mul_of_nonneg_right hratio (show 0≤2*cutProbability σ b by positivity)
    convert hm using 1
    ring
  have hQ := GeometricPartition.quadratic_nonneg hχ'.1 (le_of_lt hχ'.2) y offset h
  calc
    _ ≤ a*((2*cutProbability σ b/cutProbability τ (2*a))*GeometricPartition.quadratic (spectralCorrelation σ b) y offset h) :=
      mul_le_mul_of_nonneg_left hcomp ha
    _ = (a*(2*cutProbability σ b/cutProbability τ (2*a)))*GeometricPartition.quadratic (spectralCorrelation σ b) y offset h := by ring
    _ ≤ ((3/κ)*cutProbability σ b)*GeometricPartition.quadratic (spectralCorrelation σ b) y offset h :=
      mul_le_mul_of_nonneg_right hcoefficient hQ
    _ = _ := by ring

theorem tail_cut_ge_sixth {τ α : ℝ} (hτ : 0≤τ) (hα : 0≤α) (hz : 1/2≤τ*α) :
    1/6≤cutProbability τ α := by
  have hm := holdingFraction_mono (by norm_num : (0:ℝ)≤1/2) hz
  have hnum : holdingFraction (1/2)=1/6 := by norm_num [holdingFraction]
  rw [hnum] at hm
  exact le_trans hm (holdingFraction_le_cutProbability hτ hα)

end
end Tournament.Upper
