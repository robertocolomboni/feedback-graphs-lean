module

public import Tournament.Upper.RateTail

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

theorem faster_band_rate_comparison (m b c : ℕ) (hb : b<m) (hcb : c≤b)
    (y : ℕ → ℝ) (offset h : ℕ) :
    bandValue c*averagedCovariance m (2*bandValue b) y offset h≤
      (12/DyadicRate.base m)*averagedGain m (bandValue c) y offset h := by
  have hearly := early_rate_sum_le m b c hb hcb y offset h
  have hlate := late_rate_sum_le m b c hb hcb y offset h
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (m+1))))
    (fun j ↦ j.val+(b+1-c)<m)
    (fun j ↦ DyadicRate.weight m j*(bandValue c*
      GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h))
  calc
    _ = ∑ j : Fin (m+1), DyadicRate.weight m j*(bandValue c*
        GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) (2*bandValue b)) y offset h) := by
      unfold averagedCovariance ProbabilityVector.mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change bandValue c*(DyadicRate.weight m j*_) = _
      ring
    _ ≤ (6/DyadicRate.base m)*averagedGain m (bandValue c) y offset h+
        (6/DyadicRate.base m)*averagedGain m (bandValue c) y offset h := by
      rw [← hsplit]
      exact add_le_add hearly hlate
    _ = _ := by ring

theorem dyadic_rate_comparison (m : ℕ) (b c : Fin m)
    (y : ℕ → ℝ) (offset h : ℕ) :
    bandValue (min b.val c.val)*averagedCovariance m (2*bandValue b.val) y offset h≤
      (12/DyadicRate.base m)*averagedGain m (bandValue c.val) y offset h := by
  by_cases hbc : b.val<c.val
  · rw [Nat.min_eq_left (Nat.le_of_lt hbc)]
    have hc := slower_band_rate_comparison m b.val c.val b.isLt hbc y offset h
    have hgain := averagedGain_nonneg m (le_of_lt (bandValue_pos c.val)) y offset h
    have hκ := DyadicRate.base_pos m
    have hcoeff : 3/DyadicRate.base m≤12/DyadicRate.base m :=
      div_le_div_of_nonneg_right (by norm_num) (le_of_lt hκ)
    exact le_trans hc (mul_le_mul_of_nonneg_right hcoeff hgain)
  · have hcb : c.val≤b.val := by omega
    rw [Nat.min_eq_right hcb]
    exact faster_band_rate_comparison m b.val c.val b.isLt hcb y offset h

theorem bandValue_eq_integer_power (k : ℤ) (hk : -1≤k) :
    bandValue (k+1).toNat=(2:ℝ)^k := by
  have hcast : ((k+1).toNat : ℤ)=k+1 := Int.toNat_of_nonneg (by omega)
  unfold bandValue
  rw [← zpow_natCast,hcast,zpow_add₀ (by norm_num),zpow_one]
  ring

theorem dyadic_rate_comparison_integer (m : ℕ) (k k' : ℤ)
    (hk : -1≤k) (hkm : k≤(m:ℤ)-2) (hk' : -1≤k') (hk'm : k'≤(m:ℤ)-2)
    (y : ℕ → ℝ) (offset h : ℕ) :
    (2:ℝ)^(min k k')*averagedCovariance m ((2:ℝ)^(k+1)) y offset h≤
      (12/DyadicRate.base m)*averagedGain m ((2:ℝ)^k') y offset h := by
  have hcast : ((k+1).toNat : ℤ)=k+1 := Int.toNat_of_nonneg (by omega)
  have hcast' : ((k'+1).toNat : ℤ)=k'+1 := Int.toNat_of_nonneg (by omega)
  have hb : (k+1).toNat<m := by omega
  have hc : (k'+1).toNat<m := by omega
  have hmin : bandValue (min (k+1).toNat (k'+1).toNat)=(2:ℝ)^(min k k') := by
    by_cases hle : k≤k'
    · rw [Nat.min_eq_left (show (k+1).toNat≤(k'+1).toNat by omega),min_eq_left hle,
        bandValue_eq_integer_power k hk]
    · rw [Nat.min_eq_right (show (k'+1).toNat≤(k+1).toNat by omega),min_eq_right (by omega : k'≤k),
        bandValue_eq_integer_power k' hk']
  have hsource : 2*bandValue (k+1).toNat=(2:ℝ)^(k+1) := by
    rw [bandValue_eq_integer_power k hk,zpow_add₀ (by norm_num),zpow_one]
    ring
  have hd := dyadic_rate_comparison m ⟨(k+1).toNat,hb⟩ ⟨(k'+1).toNat,hc⟩ y offset h
  change bandValue (min (k+1).toNat (k'+1).toNat)*
    averagedCovariance m (2*bandValue (k+1).toNat) y offset h≤
      (12/DyadicRate.base m)*averagedGain m (bandValue (k'+1).toNat) y offset h at hd
  rw [hmin,hsource,bandValue_eq_integer_power k' hk'] at hd
  exact hd

end
end Tournament.Upper
