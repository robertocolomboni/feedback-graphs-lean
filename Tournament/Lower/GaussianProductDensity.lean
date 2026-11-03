module

public import Tournament.Lower.GaussianKL
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

variable {C : Type*} [Fintype C]

def productLaw (m : C → ℝ) (v : ℝ≥0) : Measure (C → ℝ) :=
  Measure.pi (fun c ↦ gaussianReal (m c) v)

instance productLaw_probability (m : C → ℝ) (v : ℝ≥0) : IsProbabilityMeasure (productLaw m v) := by
  unfold productLaw
  infer_instance

def base (C : Type*) [Fintype C] : Measure (C → ℝ) := Measure.pi (fun _ : C ↦ volume)

instance base_sigmaFinite : SigmaFinite (base C) := by
  unfold base
  infer_instance

def density (m : C → ℝ) (v : ℝ≥0) (x : C → ℝ) : ℝ≥0∞ := ∏ c, gaussianPDF (m c) v (x c)

def realDensity (m : C → ℝ) (v : ℝ≥0) (x : C → ℝ) : ℝ := ∏ c, gaussianPDFReal (m c) v (x c)

theorem density_measurable (m : C → ℝ) (v : ℝ≥0) : Measurable (density m v) :=
  Finset.measurable_prod _ (fun c _ ↦ (measurable_gaussianPDF (m c) v).comp (measurable_pi_apply c))

theorem density_pos (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) (x : C → ℝ) : 0<density m v x :=
  pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun c _ ↦ (gaussianPDF_pos _ hv (x c)).ne'))

theorem density_toReal (m : C → ℝ) (v : ℝ≥0) (x : C → ℝ) : (density m v x).toReal=realDensity m v x := by
  simp only [density,realDensity,ENNReal.toReal_prod,toReal_gaussianPDF]

theorem density_eq_ofReal (m : C → ℝ) (v : ℝ≥0) (x : C → ℝ) : density m v x=ENNReal.ofReal (realDensity m v x) := by
  unfold density realDensity
  rw [ENNReal.ofReal_prod_of_nonneg (fun c _ ↦ gaussianPDFReal_nonneg (m c) v (x c))]
  rfl

theorem realDensity_nonneg (m : C → ℝ) (v : ℝ≥0) (x : C → ℝ) : 0≤realDensity m v x :=
  Finset.prod_nonneg (fun c _ ↦ gaussianPDFReal_nonneg (m c) v (x c))

theorem realDensity_pos (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) (x : C → ℝ) : 0<realDensity m v x :=
  Finset.prod_pos (fun c _ ↦ gaussianPDFReal_pos (m c) v (x c) hv)

theorem realDensity_integrable (m : C → ℝ) (v : ℝ≥0) : Integrable (realDensity m v) (base C) :=
  Integrable.fintype_prod (fun c ↦ integrable_gaussianPDFReal (m c) v)

theorem productLaw_eq_withDensity (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    productLaw m v=(base C).withDensity (density m v) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  calc
    _ = ∫⁻ x in Set.univ.pi s, ENNReal.ofReal (realDensity m v x) ∂base C := by
      apply lintegral_congr
      intro x
      exact density_eq_ofReal m v x
    _ = ENNReal.ofReal (∫ x in Set.univ.pi s, realDensity m v x ∂base C) :=
      (ofReal_integral_eq_lintegral_ofReal (realDensity_integrable m v).restrict
        (Filter.Eventually.of_forall (realDensity_nonneg m v))).symm
    _ = ENNReal.ofReal (∏ c, ∫ x in s c, gaussianPDFReal (m c) v x) := by
      unfold base realDensity
      rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
    _ = ∏ c, ENNReal.ofReal (∫ x in s c, gaussianPDFReal (m c) v x) :=
      ENNReal.ofReal_prod_of_nonneg (fun c _ ↦ integral_nonneg (gaussianPDFReal_nonneg (m c) v))
    _ = ∏ c, gaussianReal (m c) v (s c) := by
      apply Finset.prod_congr rfl
      intro c _
      exact (gaussianReal_apply_eq_integral (m c) hv (s c)).symm

theorem productLaw_ac_base (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) : productLaw m v ≪ base C := by
  rw [productLaw_eq_withDensity m v hv]
  exact withDensity_absolutelyContinuous _ _

theorem base_ac_productLaw (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) : base C ≪ productLaw m v := by
  rw [productLaw_eq_withDensity m v hv]
  exact withDensity_absolutelyContinuous' (density_measurable m v).aemeasurable
    (Filter.Eventually.of_forall (fun x ↦ (density_pos m v hv x).ne'))

theorem productLaw_absolutelyContinuous (m n : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    productLaw m v ≪ productLaw n v := (productLaw_ac_base m v hv).trans (base_ac_productLaw n v hv)

theorem productLaw_rnDeriv (m : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    (productLaw m v).rnDeriv (base C)=ᵐ[base C] density m v := by
  rw [productLaw_eq_withDensity m v hv]
  exact Measure.rnDeriv_withDensity _ (density_measurable m v)

end
end Tournament.Lower.GaussianKL
