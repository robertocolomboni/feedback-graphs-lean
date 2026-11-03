module

public import Tournament.Upper.SpectralBands

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem eigenvalue_band_range (H : HoldingFamily ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (n : H.CenteredIndex) :
    H.eigenvalue n<bandValue m := by
  have hκ := DyadicRate.base_pos m
  have hm := mul_le_mul_of_nonneg_left (H.eigenvalue_bounds n).2 (le_of_lt hκ)
  have hhalf : DyadicRate.base m*bandValue m=1/2 := by
    unfold bandValue
    rw [← mul_div_assoc,DyadicRate.base_mul_pow]
  nlinarith

theorem coordinate_finset_sum {β : Type*} (H : HoldingFamily ι) (s : Finset β)
    (f : β → ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (fun i ↦ ∑ b ∈ s, f b i) n=∑ b ∈ s, H.coordinate (f b) n := by
  exact weightedInner_sum_right H.sampling (H.eigenvector n) s f

theorem sum_band_indicator (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ n, H.eigenvalue n<bandValue m) (n : H.CenteredIndex) (a : ℝ) :
    (∑ b : Fin m, if H.inBand b.val n then a else 0)=a := by
  obtain ⟨b,hb⟩ := exists_spectral_band m (H.eigenvalue_bounds n).1 (hrange n)
  have hb' : H.inBand b.val n := hb
  rw [Finset.sum_eq_single b]
  · rw [ite_eq_left hb']
  · intro c _ hcb
    apply ite_eq_right
    intro hc
    exact hcb (Fin.ext (H.inBand_unique hc hb'))
  · intro hn
    exact False.elim (hn (Finset.mem_univ b))

theorem sum_band_restrictions (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ n, H.eigenvalue n<bandValue m) (a : H.CenteredIndex → ℝ) :
    (∑ b : Fin m, ∑ n, if H.inBand b.val n then a n else 0)=∑ n, a n := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun n _ ↦ H.sum_band_indicator m hrange n (a n))

theorem bandProject_sum (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ n, H.eigenvalue n<bandValue m) (f : ι → ℝ) :
    (fun i ↦ ∑ b : Fin m, H.bandProject b.val f i)=H.sampling.center f := by
  apply H.eq_of_mean_coordinates
  · rw [ProbabilityVector.mean_sum,H.sampling.mean_center]
    simp only [H.bandProject_centered,Finset.sum_const_zero]
  · intro n
    rw [H.coordinate_finset_sum,H.coordinate_center]
    simp_rw [H.bandProject_coordinate]
    exact H.sum_band_indicator m hrange n (H.coordinate f n)

theorem bandProject_squareNorm_sum (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ n, H.eigenvalue n<bandValue m) (f : ι → ℝ) :
    (∑ b : Fin m, H.sampling.squareNorm (H.bandProject b.val f))=H.sampling.variance f := by
  simp_rw [H.bandProject_squareNorm]
  rw [H.sum_band_restrictions m hrange,H.variance_coordinates]

theorem coordinate_zero_of_band_fixed (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ)
    (hfixed : H.bandProject b f=f) (n : H.CenteredIndex) (hn : ¬H.inBand b n) :
    H.coordinate f n=0 := by
  have he := congrArg (fun g ↦ H.coordinate g n) hfixed
  rw [H.bandProject_coordinate,ite_eq_right hn] at he
  exact he.symm

theorem band_fixed_refresh_variance_le (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ)
    (hfixed : H.bandProject b f=f) :
    H.refresh.variance f≤(2*bandValue b)*H.sampling.squareNorm f := by
  have hmean : H.sampling.mean f=0 := by rw [← hfixed,H.bandProject_centered]
  have hnorm : H.sampling.squareNorm f=∑ n, (H.coordinate f n)^2 := by
    calc
      _ = H.sampling.variance f := by rw [H.sampling.squareNorm_eq_variance_add_mean_sq,hmean]; ring
      _ = _ := H.variance_coordinates f
  rw [H.refresh_variance_coordinates,hnorm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : H.inBand b n
  · exact mul_le_mul_of_nonneg_right (le_of_lt hn.2) (sq_nonneg _)
  · rw [H.coordinate_zero_of_band_fixed b f hfixed n hn]
    ring_nf
    exact le_refl _

theorem band_reciprocal_weight_le (H : HoldingFamily ι) (b c : ℕ) (n : H.CenteredIndex)
    (hn : H.inBand b n) :
    1/bandValue (min b c)≤2/H.eigenvalue n+1/bandValue c := by
  have hα : 0<H.eigenvalue n := by have := (H.eigenvalue_bounds n).1; linarith
  by_cases hbc : b≤c
  · rw [Nat.min_eq_left hbc]
    have hs : 1/bandValue b≤2/H.eigenvalue n := by
      apply (div_le_div_iff₀ (bandValue_pos b) hα).mpr
      linarith [hn.2]
    have hpos : 0≤1/bandValue c := by have := bandValue_pos c; positivity
    linarith
  · rw [Nat.min_eq_right (by omega : c≤b)]
    have hpos : 0≤2/H.eigenvalue n := by positivity
    linarith

theorem band_weighted_squares_le (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ n, H.eigenvalue n<bandValue m) (c : Fin m) (f : ι → ℝ) :
    (∑ b : Fin m, (1/bandValue (min b.val c.val))*H.sampling.squareNorm (H.bandProject b.val f))≤
      2*(∑ n, (H.coordinate f n)^2/H.eigenvalue n)+
        (1/bandValue c.val)*(∑ n, (H.coordinate f n)^2) := by
  calc
    _ = ∑ b : Fin m, ∑ n, if H.inBand b.val n then
        (1/bandValue (min b.val c.val))*(H.coordinate f n)^2 else 0 := by
      simp_rw [H.bandProject_squareNorm,Finset.mul_sum,mul_ite,mul_zero]
    _ ≤ ∑ b : Fin m, ∑ n, if H.inBand b.val n then
        (2/H.eigenvalue n+1/bandValue c.val)*(H.coordinate f n)^2 else 0 := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : H.inBand b.val n
      · rw [ite_eq_left hn,ite_eq_left hn]
        exact mul_le_mul_of_nonneg_right (H.band_reciprocal_weight_le b.val c.val n hn) (sq_nonneg _)
      · rw [ite_eq_right hn,ite_eq_right hn]
    _ = ∑ n, (2/H.eigenvalue n+1/bandValue c.val)*(H.coordinate f n)^2 :=
      H.sum_band_restrictions m hrange _
    _ = (∑ n, 2*((H.coordinate f n)^2/H.eigenvalue n))+
        ∑ n, (1/bandValue c.val)*(H.coordinate f n)^2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum]

end
end Tournament.HoldingFamily
