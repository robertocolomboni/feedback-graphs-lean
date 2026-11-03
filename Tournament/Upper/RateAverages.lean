module

public import Tournament.Upper.RateShift

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

def temporalGain (τ α : ℝ) (y : ℕ → ℝ) (offset h : ℕ) : ℝ :=
  cutProbability τ α*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h

def averagedCovariance (m : ℕ) (α : ℝ) (y : ℕ → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) α) y offset h)

def averagedGain (m : ℕ) (α : ℝ) (y : ℕ → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ temporalGain (DyadicRate.rate m j) α y offset h)

theorem temporalGain_nonneg {τ α : ℝ} (hτ : 0<τ) (hτ1 : τ≤1) (hα : 0≤α)
    (y : ℕ → ℝ) (offset h : ℕ) : 0≤temporalGain τ α y offset h := by
  have hc := spectralCorrelation_bounds hτ hτ1 hα
  exact mul_nonneg (le_trans (le_of_lt hτ) (rate_le_cutProbability (le_of_lt hτ) hτ1 hα))
    (GeometricPartition.quadratic_nonneg hc.1 (le_of_lt hc.2) y offset h)

theorem averagedGain_nonneg (m : ℕ) {α : ℝ} (hα : 0≤α)
    (y : ℕ → ℝ) (offset h : ℕ) : 0≤averagedGain m α y offset h :=
  ProbabilityVector.mean_nonneg _ (fun j ↦ temporalGain_nonneg
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) hα y offset h)

theorem averagedGain_atom_lower (m : ℕ) {α : ℝ} (hα : 0≤α)
    (y : ℕ → ℝ) (offset h : ℕ) :
    DyadicRate.base m*GeometricPartition.quadratic 0 y offset h≤averagedGain m α y offset h := by
  have hs : DyadicRate.weight m (Fin.last m)*temporalGain (DyadicRate.rate m (Fin.last m)) α y offset h≤
      ∑ j : Fin (m+1), DyadicRate.weight m j*temporalGain (DyadicRate.rate m j) α y offset h :=
    Finset.single_le_sum (fun j _ ↦ mul_nonneg ((DyadicRate.law m).nonneg j)
      (temporalGain_nonneg (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) hα y offset h)) (Finset.mem_univ (Fin.last m))
  change DyadicRate.base m*GeometricPartition.quadratic 0 y offset h≤
    ∑ j : Fin (m+1), DyadicRate.weight m j*temporalGain (DyadicRate.rate m j) α y offset h
  simpa only [DyadicRate.weight_last,DyadicRate.rate_last,temporalGain,
    cutProbability,spectralCorrelation,sub_self,zero_mul,add_zero,one_mul] using hs

theorem slower_band_rate_comparison (m b c : ℕ) (hb : b<m) (hbc : b<c)
    (y : ℕ → ℝ) (offset h : ℕ) :
    bandValue b*averagedCovariance m (2*bandValue b) y offset h≤
      (3/DyadicRate.base m)*averagedGain m (bandValue c) y offset h := by
  have hαβ : 2*bandValue b≤bandValue c := by
    have hp : (2:ℝ)^(b+1)≤2^c := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at hp
    unfold bandValue
    linarith
  unfold averagedCovariance averagedGain temporalGain
  rw [← ProbabilityVector.mean_const_mul,← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro j
  exact rate_covariance_to_gain (DyadicRate.base_pos m)
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j)
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j)
    (DyadicRate.base_le_rate m j) (le_of_lt (bandValue_pos b)) (le_of_lt (bandValue_pos c))
    (bandValue_dyadic_bound m b hb)
    (cutProbability_mono (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j)
      (show 0≤2*bandValue b by have := bandValue_pos b; positivity) hαβ) y offset h

theorem rateShift_sum_le (m d : ℕ) (f : Fin (m+1) → ℝ) (hf : ∀ j, 0≤f j) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ j.val+d<m), f (rateShift m d j))≤∑ j, f j := by
  let S : Finset (Fin (m+1)) := Finset.univ.filter (fun j ↦ j.val+d<m)
  have hinj : Set.InjOn (rateShift m d) S := by
    intro j hj k hk heq
    have hj' : j.val+d<m := (Finset.mem_filter.mp hj).2
    have hk' : k.val+d<m := (Finset.mem_filter.mp hk).2
    have hv := congrArg Fin.val heq
    rw [rateShift_val m d j hj',rateShift_val m d k hk'] at hv
    exact Fin.ext (by omega)
  calc
    _ = ∑ r ∈ S.image (rateShift m d), f r := (Finset.sum_image hinj).symm
    _ ≤ ∑ r, f r := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun r _ _ ↦ hf r)

theorem early_rate_sum_le (m b c : ℕ) (hb : b<m) (hcb : c≤b)
    (y : ℕ → ℝ) (offset h : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ j.val+(b+1-c)<m),
      DyadicRate.weight m j*(bandValue c*
        GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h))≤
          (6/DyadicRate.base m)*averagedGain m (bandValue c) y offset h := by
  have hf : ∀ j : Fin (m+1), 0≤DyadicRate.weight m j*temporalGain (DyadicRate.rate m j) (bandValue c) y offset h := by
    intro j
    exact mul_nonneg ((DyadicRate.law m).nonneg j) (temporalGain_nonneg
      (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) (le_of_lt (bandValue_pos c)) y offset h)
  have hsum := rateShift_sum_le m (b+1-c)
    (fun j ↦ DyadicRate.weight m j*temporalGain (DyadicRate.rate m j) (bandValue c) y offset h) hf
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ j.val+(b+1-c)<m),
        (6/DyadicRate.base m)*(DyadicRate.weight m (rateShift m (b+1-c) j)*
          temporalGain (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c) y offset h) := by
      apply Finset.sum_le_sum
      intro j hj
      exact early_rate_weighted_comparison m b c hb hcb j (Finset.mem_filter.mp hj).2 y offset h
    _ = (6/DyadicRate.base m)*(∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ j.val+(b+1-c)<m),
        DyadicRate.weight m (rateShift m (b+1-c) j)*
          temporalGain (DyadicRate.rate m (rateShift m (b+1-c) j)) (bandValue c) y offset h) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by have := DyadicRate.base_pos m; positivity)

end
end Tournament.Upper
