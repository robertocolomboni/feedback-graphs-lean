module

public import Tournament.Upper.RateAverages

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

theorem late_rate_product_lower (m b c : ℕ) (hcb : c≤b) (j : Fin (m+1))
    (hj : ¬ j.val+(b+1-c)<m) :
    bandValue c≤DyadicRate.rate m j*(2*bandValue b) := by
  have hp : (2:ℝ)^m≤2^(j.val+(b+1-c)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hm := mul_le_mul_of_nonneg_left hp (le_of_lt (DyadicRate.base_pos m))
  rw [DyadicRate.base_mul_pow] at hm
  calc
    bandValue c = 1*bandValue c := (one_mul _).symm
    _ ≤ (DyadicRate.base m*2^(j.val+(b+1-c)))*bandValue c :=
      mul_le_mul_of_nonneg_right hm (le_of_lt (bandValue_pos c))
    _ = DyadicRate.rate m j*((2:ℝ)^(b+1-c)*bandValue c) := by
      rw [pow_add]
      unfold DyadicRate.rate
      ring
    _ = _ := by rw [band_shift_scale b c hcb]

theorem late_rate_quadratic_le (m b c : ℕ) (hcb : c≤b) (j : Fin (m+1))
    (hj : ¬ j.val+(b+1-c)<m) (y : ℕ → ℝ) (offset h : ℕ) :
    GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h≤
      12*GeometricPartition.quadratic 0 y offset h := by
  have hτ := DyadicRate.rate_pos m j
  have hτ1 := DyadicRate.rate_le_one m j
  have hα : 0≤2*bandValue b := by have := bandValue_pos b; positivity
  have hχ := spectralCorrelation_bounds hτ hτ1 hα
  have hcut := tail_cut_ge_sixth (le_of_lt hτ) hα
    (le_trans (bandValue_ge_half c) (late_rate_product_lower m b c hcb j hj))
  have hcpos : 0<cutProbability (DyadicRate.rate m j) (2*bandValue b) := by linarith
  have hcomp := GeometricPartition.quadratic_le_zero_correlation hχ.1 hχ.2 y offset h
  rw [one_sub_correlation (le_of_lt hτ) hα] at hcomp
  have hcoeff : 2/cutProbability (DyadicRate.rate m j) (2*bandValue b)≤12 := by
    apply (div_le_iff₀ hcpos).mpr
    linarith
  exact le_trans hcomp (mul_le_mul_of_nonneg_right hcoeff
    (GeometricPartition.quadratic_nonneg (by norm_num) (by norm_num) y offset h))

theorem late_rate_weight_sum (m d : ℕ) (hd : d≤m) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ ¬ j.val+d<m), DyadicRate.weight m j)=
      DyadicRate.base m*(2:ℝ)^d := by
  rw [Finset.sum_filter]
  have heq : (∑ j : Fin (m+1), if ¬ j.val+d<m then DyadicRate.weight m j else 0)=
      ∑ j : Fin (m+1), if m-d≤j.val then DyadicRate.weight m j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hp : (¬j.val+d<m)↔m-d≤j.val := by omega
    simp only [hp]
  rw [heq,DyadicRate.tail_weight_sum m (m-d) (by omega)]
  have hsplit : (m-d)+d=m := Nat.sub_add_cancel hd
  have hone := DyadicRate.base_mul_pow d
  change (1/2:ℝ)^d*2^d=1 at hone
  calc
    (1/2:ℝ)^(m-d) = (1/2:ℝ)^(m-d)*((1/2:ℝ)^d*2^d) := by rw [hone,mul_one]
    _ = (1/2:ℝ)^((m-d)+d)*2^d := by rw [pow_add]; ring
    _ = _ := by rw [hsplit]; rfl

theorem late_rate_sum_le (m b c : ℕ) (hb : b<m) (hcb : c≤b)
    (y : ℕ → ℝ) (offset h : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ ¬ j.val+(b+1-c)<m),
      DyadicRate.weight m j*(bandValue c*
        GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h))≤
          (6/DyadicRate.base m)*averagedGain m (bandValue c) y offset h := by
  have hκ := DyadicRate.base_pos m
  have hd : b+1-c≤m := by omega
  have hQ : 0≤GeometricPartition.quadratic 0 y offset h :=
    GeometricPartition.quadratic_nonneg (by norm_num) (by norm_num) y offset h
  have hcap := bandValue_dyadic_bound m b hb
  have hatom := averagedGain_atom_lower m (le_of_lt (bandValue_pos c)) y offset h
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ ¬ j.val+(b+1-c)<m),
        DyadicRate.weight m j*(bandValue c*(12*GeometricPartition.quadratic 0 y offset h)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (late_rate_quadratic_le m b c hcb j (Finset.mem_filter.mp hj).2 y offset h)
        (le_of_lt (bandValue_pos c))) ((DyadicRate.law m).nonneg j)
    _ = (∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) ↦ ¬ j.val+(b+1-c)<m), DyadicRate.weight m j)*
        (bandValue c*(12*GeometricPartition.quadratic 0 y offset h)) := (Finset.sum_mul _ _ _).symm
    _ = 12*(DyadicRate.base m*(2*bandValue b))*GeometricPartition.quadratic 0 y offset h := by
      rw [late_rate_weight_sum m (b+1-c) hd]
      calc
        _ = 12*DyadicRate.base m*((2:ℝ)^(b+1-c)*bandValue c)*GeometricPartition.quadratic 0 y offset h := by ring
        _ = _ := by rw [band_shift_scale b c hcb]; ring
    _ ≤ 6*GeometricPartition.quadratic 0 y offset h :=
      mul_le_mul_of_nonneg_right (by linarith : 12*(DyadicRate.base m*(2*bandValue b))≤6) hQ
    _ = (6/DyadicRate.base m)*(DyadicRate.base m*GeometricPartition.quadratic 0 y offset h) := by
      field_simp [ne_of_gt hκ]
    _ ≤ _ := mul_le_mul_of_nonneg_left hatom (by positivity)

end
end Tournament.Upper
