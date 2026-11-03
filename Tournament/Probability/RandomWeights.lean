module

public import Tournament.Foundations.Centering
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

namespace Tournament.MeasureRandomWeights

open scoped BigOperators MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω)

omit mΩ in
theorem norm_weight_le_one (p : Ω → ProbabilityVector ι) (i : ι) (ω : Ω) : ‖p ω i‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg ((p ω).nonneg i)]
  exact (p ω).weight_le_one i

theorem integrable_weight_mul (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable (fun ω ↦ p ω i) μ) (g : Ω → ℝ)
    (hg : Integrable g μ) (i : ι) : Integrable (fun ω ↦ p ω i*g ω) μ :=
  hg.bdd_mul (hp i) (Eventually.of_forall (norm_weight_le_one p i))

theorem integrable_mean (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable (fun ω ↦ p ω i) μ) (g : Ω → ι → ℝ)
    (hg : ∀ i, Integrable (fun ω ↦ g ω i) μ) : Integrable (fun ω ↦ (p ω).mean (g ω)) μ :=
  integrable_finsetSum Finset.univ (fun i _ ↦ integrable_weight_mul μ p hp _ (hg i) i)

theorem integrable_comparison (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable (fun ω ↦ p ω i) μ) (g : Ω → ι → ℝ)
    (hg : ∀ i, Integrable (fun ω ↦ g ω i) μ) (i : ι) :
    Integrable (fun ω ↦ (p ω).mean (g ω)-g ω i) μ :=
  (integrable_mean μ p hp g hg).sub (hg i)

variable {m : MeasurableSpace Ω}

theorem integral_mean_condExp (hm : m≤mΩ) [SigmaFinite (μ.trim hm)] (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ p ω i) μ) (g : Ω → ι → ℝ)
    (hg : ∀ i, Integrable (fun ω ↦ g ω i) μ) :
    (∫ ω, (p ω).mean (g ω) ∂μ)=
      ∫ ω, (p ω).mean (fun i ↦ (μ[fun x ↦ g x i | m]) ω) ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hp' (i : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ p ω i) μ := AEStronglyMeasurable.mono hm (hp i)
  unfold ProbabilityVector.mean
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_weight_mul μ p hp' _ (hg i) i)]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_weight_mul μ p hp' _ integrable_condExp i)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ ω, (μ[fun x ↦ p x i*g x i | m]) ω ∂μ := (integral_condExp hm).symm
    _ = _ := integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left (hp i)
      (integrable_weight_mul μ p hp' _ (hg i) i) (hg i))

theorem integral_comparison_condExp (hm : m≤mΩ) [SigmaFinite (μ.trim hm)] (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ p ω i) μ) (g : Ω → ι → ℝ)
    (hg : ∀ i, Integrable (fun ω ↦ g ω i) μ) (i : ι) :
    (∫ ω, ((p ω).mean (g ω)-g ω i) ∂μ)=
      ∫ ω, ((p ω).mean (fun j ↦ (μ[fun x ↦ g x j | m]) ω)-(μ[fun x ↦ g x i | m]) ω) ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hp' (j : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ p ω j) μ := AEStronglyMeasurable.mono hm (hp j)
  rw [integral_sub (integrable_mean μ p hp' g hg) (hg i),
    integral_sub (integrable_mean μ p hp' _ (fun _ ↦ integrable_condExp)) integrable_condExp,
    integral_mean_condExp μ hm p hp g hg,integral_condExp hm]

end
end Tournament.MeasureRandomWeights
