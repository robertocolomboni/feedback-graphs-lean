module

public import Tournament.Lower.GaussianProductKL
public import Tournament.Lower.ClippingExperiment
public import Tournament.Lower.ShiftEnergy

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

theorem incrementVariance_ne_zero (T : ℕ) (hT : 1≤T) : incrementVariance T≠0 := by
  have hs := Parameters.sigma_pos T hT
  have hv : (0:ℝ)<(incrementVariance T:ℝ) := sq_pos_of_pos hs
  exact ne_of_gt (by exact_mod_cast hv)

theorem gaussian_shift_kl {ι : Type*} {S : Finset ι} (m δ : Coordinate S → ℝ)
    (v : ℝ≥0) (hv : v≠0) :
    klDiv (GaussianKL.productLaw m v) (GaussianKL.productLaw (m+δ) v)=
      ENNReal.ofReal (shiftEnergy δ/(2*(v:ℝ))) := by
  rw [GaussianKL.product_klDiv_same_variance m (m+δ) v hv]
  have heq : (∑ c, (m c-(m+δ) c)^2)=shiftEnergy δ := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [Pi.add_apply]
    ring
  rw [heq]

theorem gaussian_parent_shift_kl {ι : Type*} {S : Finset ι} (T : ℕ) (hT : 1≤T)
    (parentObservation currentShift parentShift : Coordinate S → ℝ) :
    klDiv (GaussianKL.productLaw parentObservation (incrementVariance T))
      (GaussianKL.productLaw (parentObservation+(currentShift-parentShift)) (incrementVariance T))=
      ENNReal.ofReal (shiftEnergy (currentShift-parentShift)/(2*(Parameters.sigma T)^2)) :=
  gaussian_shift_kl _ _ _ (incrementVariance_ne_zero T hT)

end
end Tournament.Lower
