module

public import Tournament.Upper.SpectralTemporal

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι β : Type*} [Fintype ι] [Fintype β]

theorem vectorAveragedGain_interval_domination (p : ProbabilityVector ι) (m : ℕ) {α : ℝ} (hα : 0≤α)
    (a : β → ℝ) (A : β → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ℕ → ι → ℝ) (C : ℝ)
    (hinterval : ∀ start n, (∑ b, a b*p.squareNorm (A b (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i)))≤
      C*p.squareNorm (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i)) (offset n : ℕ) :
    (∑ b, a b*vectorAveragedGain p m α (fun t ↦ A b (f t)) offset (n+1))≤
      C*vectorAveragedGain p m α f offset (n+1) := by
  unfold vectorAveragedGain
  calc
    _ = (DyadicRate.law m).mean (fun j ↦ ∑ b, a b*(cutProbability (DyadicRate.rate m j) α*
        GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) (fun t ↦ A b (f t)) offset (n+1))) := by
      rw [ProbabilityVector.mean_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [ProbabilityVector.mean_const_mul]
    _ ≤ (DyadicRate.law m).mean (fun j ↦ C*(cutProbability (DyadicRate.rate m j) α*
        GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) f offset (n+1))) := by
      apply ProbabilityVector.mean_mono
      intro j
      have hχ := spectralCorrelation_bounds (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) hα
      have hdom := GeometricPartition.interval_bound_temporal_domination p a A f C hinterval hχ.1 (le_of_lt hχ.2) offset n
      have hc : 0≤cutProbability (DyadicRate.rate m j) α :=
        le_trans (le_of_lt (DyadicRate.rate_pos m j))
          (rate_le_cutProbability (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) hα)
      calc
        _ = cutProbability (DyadicRate.rate m j) α*(∑ b, a b*
            GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) (fun t ↦ A b (f t)) offset (n+1)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ ↦ by ring)
        _ ≤ cutProbability (DyadicRate.rate m j) α*(C*
            GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) f offset (n+1)) :=
          mul_le_mul_of_nonneg_left hdom hc
        _ = _ := by ring
    _ = _ := ProbabilityVector.mean_const_mul _ C _

theorem vector_dyadic_rate_comparison (p : ProbabilityVector ι) (m : ℕ) (b c : Fin m)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    bandValue (min b.val c.val)*vectorAveragedCovariance p m (2*bandValue b.val) f offset h≤
      (12/DyadicRate.base m)*vectorAveragedGain p m (bandValue c.val) f offset h := by
  rw [vectorAveragedCovariance_coordinates,vectorAveragedGain_coordinates,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd := dyadic_rate_comparison m b c (fun t ↦ f t i) offset h
  calc
    _ = p i*(bandValue (min b.val c.val)*averagedCovariance m (2*bandValue b.val) (fun t ↦ f t i) offset h) := by ring
    _ ≤ p i*((12/DyadicRate.base m)*averagedGain m (bandValue c.val) (fun t ↦ f t i) offset h) :=
      mul_le_mul_of_nonneg_left hd (p.nonneg i)
    _ = _ := by ring

theorem vector_covariance_paid (p : ProbabilityVector ι) (m : ℕ) (b c : Fin m)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    vectorAveragedCovariance p m (2*bandValue b.val) f offset h≤
      (12/DyadicRate.base m)*((1/bandValue (min b.val c.val))*vectorAveragedGain p m (bandValue c.val) f offset h) := by
  have hd := vector_dyadic_rate_comparison p m b c f offset h
  rw [show (12/DyadicRate.base m)*((1/bandValue (min b.val c.val))*vectorAveragedGain p m (bandValue c.val) f offset h)=
    ((12/DyadicRate.base m)*vectorAveragedGain p m (bandValue c.val) f offset h)/bandValue (min b.val c.val) by ring]
  apply (le_div_iff₀ (bandValue_pos (min b.val c.val))).mpr
  calc
    _ = bandValue (min b.val c.val)*vectorAveragedCovariance p m (2*bandValue b.val) f offset h := mul_comm _ _
    _ ≤ _ := hd

theorem referenceErrorEnergy_band_gain_le (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ H.sampling w) (c : Fin m) (f : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ f offset n≤(48/DyadicRate.base m)*
      (∑ i, w i*(∑ b : Fin m, (1/bandValue (min b.val c.val))*vectorAveragedGain H.sampling m (bandValue c.val)
        (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1))) := by
  have hcov := referenceErrorEnergy_band_covariance_le H w m hmax Ψ hcal f offset n
  have hsum : (∑ i, w i*(∑ b : Fin m, vectorAveragedCovariance H.sampling m (2*bandValue b.val)
      (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1)))≤
        (12/DyadicRate.base m)*(∑ i, w i*(∑ b : Fin m, (1/bandValue (min b.val c.val))*
          vectorAveragedGain H.sampling m (bandValue c.val)
            (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hlocal := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ vector_covariance_paid H.sampling m b c
      (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1))
    rw [← Finset.mul_sum] at hlocal
    have hw := mul_le_mul_of_nonneg_left hlocal (w.nonneg i)
    convert hw using 1
    ring
  calc
    _ ≤ _ := hcov
    _ ≤ 4*((12/DyadicRate.base m)*(∑ i, w i*(∑ b : Fin m, (1/bandValue (min b.val c.val))*
        vectorAveragedGain H.sampling m (bandValue c.val)
          (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1)))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

theorem band_interval_fixed (H : HoldingFamily ι) (c : ℕ) (f : ℕ → ι → ℝ)
    (hfixed : ∀ t, H.bandProject c (f t)=f t) (start n : ℕ) :
    H.bandProject c (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i)=
      (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i) := by
  rw [H.bandProject_finset_sum]
  simp_rw [hfixed]

theorem band_gain_errors_le (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ H.sampling w) (L₀ : ℝ) (hL₀ : 0≤L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (c : Fin m) (f : ℕ → ι → ℝ)
    (hfixed : ∀ t, H.bandProject c.val (f t)=f t) (offset n : ℕ) :
    (∑ i, w i*(∑ b : Fin m, (1/bandValue (min b.val c.val))*vectorAveragedGain H.sampling m (bandValue c.val)
      (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1)))≤
        (4*L₀)*vectorAveragedGain H.sampling m (bandValue c.val) f offset (n+1) := by
  let a : ι × Fin m → ℝ := fun ib ↦ w ib.1*(1/bandValue (min ib.2.val c.val))
  let A : ι × Fin m → (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := fun ib ↦
    (H.bandProjectMap ib.2.val).comp (sourceErrorMap Ψ w ib.1)
  have hinterval : ∀ start k, (∑ ib, a ib*H.sampling.squareNorm
      (A ib (fun i ↦ ∑ t ∈ Finset.range (k+1), f (start+t) i)))≤
        (4*L₀)*H.sampling.squareNorm (fun i ↦ ∑ t ∈ Finset.range (k+1), f (start+t) i) := by
    intro start k
    have hfix := band_interval_fixed H c.val f hfixed start k
    have hcenter : H.sampling.mean (fun i ↦ ∑ t ∈ Finset.range (k+1), f (start+t) i)=0 := by
      rw [← hfix,H.bandProject_centered]
    have he := errors_caused_by_one_band H m hmax w Ψ hcal L₀ hL₀ hend c _ hcenter hfix
    rw [Fintype.sum_prod_type]
    change (∑ i, ∑ b : Fin m, (w i*(1/bandValue (min b.val c.val)))*H.sampling.squareNorm
      (H.bandProject b.val (sourceError Ψ w i (fun j ↦ ∑ t ∈ Finset.range (k+1), f (start+t) j))))≤_
    simpa only [Finset.mul_sum,mul_assoc] using he
  have hdom := vectorAveragedGain_interval_domination H.sampling m (le_of_lt (bandValue_pos c.val)) a A f
    (4*L₀) hinterval offset n
  rw [Fintype.sum_prod_type] at hdom
  change (∑ i, ∑ b : Fin m, (w i*(1/bandValue (min b.val c.val)))*vectorAveragedGain H.sampling m (bandValue c.val)
    (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1))≤_ at hdom
  simpa only [Finset.mul_sum,mul_assoc] using hdom

end
end Tournament.Upper
