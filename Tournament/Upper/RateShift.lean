module

public import Tournament.Upper.RateComparisonCore

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

def rateShift (m d : ℕ) (j : Fin (m+1)) : Fin (m+1) :=
  ⟨min (j.val+d) m,by omega⟩

theorem rateShift_val (m d : ℕ) (j : Fin (m+1)) (hj : j.val+d<m) :
    (rateShift m d j).val=j.val+d := Nat.min_eq_left (by omega)

theorem rateShift_rate (m d : ℕ) (j : Fin (m+1)) (hj : j.val+d<m) :
    DyadicRate.rate m (rateShift m d j)=(2:ℝ)^d*DyadicRate.rate m j := by
  unfold DyadicRate.rate
  rw [rateShift_val m d j hj,pow_add]
  ring

theorem rateShift_weight (m d : ℕ) (j : Fin (m+1)) (hj : j.val+d<m) :
    DyadicRate.weight m j=(2:ℝ)^d*DyadicRate.weight m (rateShift m d j) := by
  have heq : rateShift m d j=⟨j.val+d,by omega⟩ := Fin.ext (rateShift_val m d j hj)
  rw [heq]
  exact DyadicRate.shifted_weight m d j hj

theorem band_shift_scale (b c : ℕ) (hcb : c≤b) :
    (2:ℝ)^(b+1-c)*bandValue c=2*bandValue b := by
  have hpow : (2:ℝ)^(b+1-c)*(2:ℝ)^c=2^(b+1) := by
    rw [← pow_add,Nat.sub_add_cancel (by omega)]
  unfold bandValue
  rw [← mul_div_assoc,hpow,pow_succ]
  ring

theorem rateShift_cut (m b c : ℕ) (hcb : c≤b) (j : Fin (m+1))
    (hj : j.val+(b+1-c)<m) :
    cutProbability (DyadicRate.rate m j) (2*bandValue b)≤
      cutProbability (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c) := by
  have hscale := band_shift_scale b c hcb
  have hrate := rateShift_rate m (b+1-c) j hj
  have hle : DyadicRate.rate m j≤DyadicRate.rate m (rateShift m (b+1-c) j) := by
    rw [hrate]
    exact le_mul_of_one_le_left (le_of_lt (DyadicRate.rate_pos m j)) (one_le_pow₀ (by norm_num))
  apply cutProbability_matched_product (le_of_lt (DyadicRate.rate_pos m j)) hle
    (show 0≤2*bandValue b by have := bandValue_pos b; positivity)
  rw [hrate]
  calc
    _ = DyadicRate.rate m j*((2:ℝ)^(b+1-c)*bandValue c) := by ring
    _ = _ := by rw [hscale]

theorem rateShift_weight_band (m b c : ℕ) (hcb : c≤b) (j : Fin (m+1))
    (hj : j.val+(b+1-c)<m) :
    DyadicRate.weight m j*bandValue c=
      2*DyadicRate.weight m (rateShift m (b+1-c) j)*bandValue b := by
  rw [rateShift_weight m (b+1-c) j hj]
  calc
    _ = DyadicRate.weight m (rateShift m (b+1-c) j)*((2:ℝ)^(b+1-c)*bandValue c) := by ring
    _ = _ := by rw [band_shift_scale b c hcb]; ring

theorem early_rate_weighted_comparison (m b c : ℕ) (hb : b<m) (hcb : c≤b)
    (j : Fin (m+1)) (hj : j.val+(b+1-c)<m) (y : ℕ → ℝ) (offset h : ℕ) :
    DyadicRate.weight m j*(bandValue c*
      GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h)≤
        (6/DyadicRate.base m)*(DyadicRate.weight m (rateShift m (b+1-c) j)*
          (cutProbability (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c)*
            GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c)) y offset h)) := by
  have hcomp := rate_covariance_to_gain (DyadicRate.base_pos m)
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j)
    (DyadicRate.rate_pos m (rateShift m (b+1-c) j)) (DyadicRate.rate_le_one m (rateShift m (b+1-c) j))
    (DyadicRate.base_le_rate m j) (le_of_lt (bandValue_pos b)) (le_of_lt (bandValue_pos c))
    (bandValue_dyadic_bound m b hb) (rateShift_cut m b c hcb j hj) y offset h
  have hw : 0≤DyadicRate.weight m (rateShift m (b+1-c) j) := (DyadicRate.law m).nonneg _
  calc
    _ = (2*DyadicRate.weight m (rateShift m (b+1-c) j))*(bandValue b*
        GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h) := by
      rw [← mul_assoc,rateShift_weight_band m b c hcb j hj]
      ring
    _ ≤ (2*DyadicRate.weight m (rateShift m (b+1-c) j))*((3/DyadicRate.base m)*
        (cutProbability (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c)*
          GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c)) y offset h)) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by ring

end
end Tournament.Upper
