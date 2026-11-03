module

public import Tournament.Upper.BandEnergy

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι β : Type*} [Fintype ι] [Fintype β]

theorem averagedCovariance_sum_le_card (m : ℕ) {α : ℝ} (hα : 0≤α)
    (f : β → ℕ → ℝ) (offset h : ℕ) :
    averagedCovariance m α (fun t ↦ ∑ b, f b t) offset h≤
      (Fintype.card β:ℝ)*(∑ b, averagedCovariance m α (f b) offset h) := by
  unfold averagedCovariance
  calc
    _ ≤ (DyadicRate.law m).mean (fun j ↦ (Fintype.card β:ℝ)*
        (∑ b, GeometricPartition.quadratic (spectralCorrelation (DyadicRate.rate m j) α) (f b) offset h)) := by
      apply ProbabilityVector.mean_mono
      intro j
      have hχ := spectralCorrelation_bounds (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) hα
      exact GeometricPartition.quadratic_sum_le_card hχ.1 (le_of_lt hχ.2) f offset h
    _ = _ := by rw [ProbabilityVector.mean_const_mul,ProbabilityVector.mean_sum]

theorem referenceErrorEnergy_sum_le_card (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w)
    (f : β → ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ (fun t i ↦ ∑ b, f b t i) offset n≤
      (Fintype.card β:ℝ)*(∑ b, referenceErrorEnergy H w m Ψ (f b) offset n) := by
  have hsource (i : ι) (j : H.CenteredIndex) :
      (fun t ↦ H.coordinate (sourceError Ψ w i (fun k ↦ ∑ b, f b t k)) j)=
        (fun t ↦ ∑ b, H.coordinate (sourceError Ψ w i (f b t)) j) := by
    funext t
    rw [sourceError_finset_sum,H.coordinate_finset_sum]
  have hlocal (i : ι) :
      (∑ j, averagedCovariance m (H.eigenvalue j)
        (fun t ↦ H.coordinate (sourceError Ψ w i (fun k ↦ ∑ b, f b t k)) j) offset (n+1))≤
          (Fintype.card β:ℝ)*(∑ b, ∑ j, averagedCovariance m (H.eigenvalue j)
            (fun t ↦ H.coordinate (sourceError Ψ w i (f b t)) j) offset (n+1)) := by
    simp_rw [hsource]
    calc
      _ ≤ ∑ j, (Fintype.card β:ℝ)*(∑ b, averagedCovariance m (H.eigenvalue j)
          (fun t ↦ H.coordinate (sourceError Ψ w i (f b t)) j) offset (n+1)) := by
        apply Finset.sum_le_sum
        intro j _
        exact averagedCovariance_sum_le_card m (by have := (H.eigenvalue_bounds j).1; linarith) _ offset (n+1)
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]
  rw [referenceErrorEnergy_averaged_coordinates H w m Ψ hcal]
  calc
    _ ≤ ∑ i, w i*((Fintype.card β:ℝ)*(∑ b, ∑ j, averagedCovariance m (H.eigenvalue j)
        (fun t ↦ H.coordinate (sourceError Ψ w i (f b t)) j) offset (n+1))) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hlocal i) (w.nonneg i))
    _ = (Fintype.card β:ℝ)*(∑ i, w i*(∑ b, ∑ j, averagedCovariance m (H.eigenvalue j)
        (fun t ↦ H.coordinate (sourceError Ψ w i (f b t)) j) offset (n+1))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ ↦ by ring)
    _ = (Fintype.card β:ℝ)*(∑ b, ∑ i, w i*(∑ j, averagedCovariance m (H.eigenvalue j)
        (fun t ↦ H.coordinate (sourceError Ψ w i (f b t)) j) offset (n+1))) := by
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by simp_rw [referenceErrorEnergy_averaged_coordinates H w m Ψ hcal]

theorem referenceErrorEnergy_center (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w)
    (hkill : EstimatorKillsConstants Ψ) (f : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ (fun t ↦ H.sampling.center (f t)) offset n=
      referenceErrorEnergy H w m Ψ f offset n := by
  rw [referenceErrorEnergy_averaged_coordinates H w m Ψ hcal,referenceErrorEnergy_averaged_coordinates H w m Ψ hcal]
  simp_rw [sourceError_center Ψ w H.sampling hkill]

theorem reference_errors_paid_by_energy (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ H.sampling w) (hkill : EstimatorKillsConstants Ψ)
    (L₀ : ℝ) (hL₀ : 0≤L₀) (hend : EstimatorEndpointBounds H w Ψ L₀)
    (f : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ f offset n≤
      (3072*(m:ℝ)*L₀/DyadicRate.base m)*probingEnergy H m f offset (n+1) := by
  let F : Fin m → ℕ → ι → ℝ := fun b t ↦ H.bandProject b.val (f t)
  have hsum : (fun t i ↦ ∑ b, F b t i)=(fun t ↦ H.sampling.center (f t)) := by
    funext t
    exact H.bandProject_sum m (H.eigenvalue_band_range m hmax) (f t)
  have hcs := referenceErrorEnergy_sum_le_card H w m Ψ hcal F offset n
  have hsingle : ∀ b : Fin m, referenceErrorEnergy H w m Ψ (F b) offset n≤
      (3072*L₀/DyadicRate.base m)*probingEnergy H m (F b) offset (n+1) := by
    intro b
    exact reference_error_one_band H w m hmax Ψ hcal L₀ hL₀ hend b (F b)
      (fun t ↦ H.bandProject_idempotent b.val (f t)) offset n
  calc
    _ = referenceErrorEnergy H w m Ψ (fun t i ↦ ∑ b, F b t i) offset n := by
      rw [hsum,referenceErrorEnergy_center H w m Ψ hcal hkill]
    _ ≤ (m:ℝ)*(∑ b : Fin m, referenceErrorEnergy H w m Ψ (F b) offset n) := by
      simpa only [Fintype.card_fin] using hcs
    _ ≤ (m:ℝ)*(∑ b : Fin m, (3072*L₀/DyadicRate.base m)*probingEnergy H m (F b) offset (n+1)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ ↦ hsingle b)) (Nat.cast_nonneg m)
    _ = (m:ℝ)*((3072*L₀/DyadicRate.base m)*probingEnergy H m f offset (n+1)) := by
      rw [← Finset.mul_sum]
      dsimp only [F]
      rw [probingEnergy_band_sum H m hmax]
    _ = _ := by ring

end
end Tournament.Upper
