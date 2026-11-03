module

public import Tournament.Upper.ExpectedEW

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]

theorem bias_integrable (μ : Measure Ω) (m : MeasurableSpace Ω)
    (w : Ω → ProbabilityVector ι) (hw : ∀ i, AEStronglyMeasurable[mΩ] (fun ω ↦ w ω i) μ)
    (g L ξ : Ω → ι → ℝ) (hL : ∀ i, Integrable (fun ω ↦ L ω i) μ)
    (hcal : ∀ i, μ[fun ω ↦ g ω i | m] =ᵐ[μ] fun ω ↦ (w ω).center (L ω) i-ξ ω i) :
    Integrable ξ μ := by
  let : MeasurableSpace Ω := mΩ
  apply Integrable.of_eval
  intro i
  have hmean := MeasureRandomWeights.integrable_mean μ w hw L hL
  have hint : Integrable (fun ω ↦ L ω i-(w ω).mean (L ω)-(μ[fun x ↦ g x i | m]) ω) μ :=
    ((hL i).sub hmean).sub integrable_condExp
  apply hint.congr
  filter_upwards [hcal i] with ω hω
  change (μ[fun x ↦ g x i | m]) ω=(L ω i-(w ω).mean (L ω))-ξ ω i at hω
  linarith

theorem comparison_integral_lower [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m≤mΩ) (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ p ω i) μ)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (g L ξ : Ω → ι → ℝ) (h : ℝ)
    (hg : ∀ i, Integrable (fun ω ↦ g ω i) μ) (hL : ∀ i, Integrable (fun ω ↦ L ω i) μ)
    (hLbound : ∀ᵐ ω ∂μ, ∀ j, 0≤L ω j ∧ L ω j≤h)
    (hcal : ∀ i, μ[fun ω ↦ g ω i | m] =ᵐ[μ]
      fun ω ↦ (smooth (p ω) ε hε hε1).center (L ω) i-ξ ω i) (i : ι) :
    (∫ ω, (smooth (p ω) ε hε hε1).mean (L ω) ∂μ)-(∫ ω, L ω i ∂μ)≤
      (∫ ω, ((p ω).mean (g ω)-g ω i) ∂μ)+ε*h+2*(∫ ω, ‖ξ ω‖ ∂μ) := by
  let : MeasurableSpace Ω := mΩ
  have hp' (j : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ p ω j) μ := AEStronglyMeasurable.mono hm (hp j)
  let w := fun ω ↦ smooth (p ω) ε hε hε1
  have hw (j : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ w ω j) μ :=
    smooth_aestronglyMeasurable μ p ε hε hε1 hp' j
  have hξ := bias_integrable μ m w hw g L ξ hL hcal
  have hmean := MeasureRandomWeights.integrable_mean μ w hw L hL
  have hfirst : Integrable (fun ω ↦ (w ω).mean (L ω)-L ω i) μ := hmean.sub (hL i)
  have hsecond : Integrable (fun ω ↦ (w ω).mean (L ω)-L ω i-ε*h) μ := hfirst.sub (integrable_const (ε*h))
  have hleft : Integrable (fun ω ↦ (w ω).mean (L ω)-L ω i-ε*h-2*‖ξ ω‖) μ :=
    hsecond.sub (hξ.norm.const_mul 2)
  have hcond := MeasureRandomWeights.integrable_comparison μ p hp'
    (fun ω j ↦ (μ[fun x ↦ g x j | m]) ω) (fun _ ↦ integrable_condExp) i
  have hcalAll : ∀ᵐ ω ∂μ, ∀ j, (μ[fun x ↦ g x j | m]) ω=(w ω).center (L ω) j-ξ ω j :=
    ae_all_iff.mpr hcal
  have hpoint : ∀ᵐ ω ∂μ, (w ω).mean (L ω)-L ω i-ε*h-2*‖ξ ω‖≤
      (p ω).mean (fun j ↦ (μ[fun x ↦ g x j | m]) ω)-(μ[fun x ↦ g x i | m]) ω := by
    filter_upwards [hLbound,hcalAll] with ω hω hcalω
    have heq : (fun j ↦ (μ[fun x ↦ g x j | m]) ω)=(fun j ↦ (w ω).center (L ω) j-ξ ω j) := funext hcalω
    rw [heq,hcalω i]
    exact conditional_comparison_lower (p ω) ε hε hε1 (L ω) (ξ ω) h hω i
  have hint := integral_mono_ae hleft hcond hpoint
  rw [← MeasureRandomWeights.integral_comparison_condExp μ hm p hp g hg i] at hint
  rw [integral_sub hsecond (hξ.norm.const_mul 2),
    integral_sub hfirst (integrable_const (ε*h)),integral_sub hmean (hL i),
    integral_const_mul (2:ℝ) (fun ω ↦ ‖ξ ω‖)] at hint
  have hconst : (∫ _ω : Ω, ε*h ∂μ)=ε*h := by simp
  rw [hconst] at hint
  change (∫ ω, (w ω).mean (L ω) ∂μ)-(∫ ω, L ω i ∂μ)≤_
  linarith

theorem integrated_block_condition (μ : Measure Ω) {m : MeasurableSpace Ω} (hm : m≤mΩ)
    [SigmaFinite (μ.trim hm)] (A σ Q C : Ω → ℝ) (η : ℝ)
    (hA : Integrable A μ) (hσ : Integrable σ μ) (hQ : Integrable Q μ) (hC : Integrable C μ)
    (hcond : μ[C | m] ≤ᵐ[μ] fun ω ↦ A ω+σ ω-2*η*(μ[Q | m]) ω) :
    (∫ ω, C ω ∂μ)≤(∫ ω, A ω ∂μ)+(∫ ω, σ ω ∂μ)-2*η*(∫ ω, Q ω ∂μ) := by
  let : MeasurableSpace Ω := mΩ
  have hAS : Integrable (fun ω ↦ A ω+σ ω) μ := hA.add hσ
  have hright : Integrable (fun ω ↦ A ω+σ ω-2*η*(μ[Q | m]) ω) μ :=
    hAS.sub (integrable_condExp.const_mul (2*η))
  have hCE : (∫ ω, (μ[C | m]) ω ∂μ)=∫ ω, C ω ∂μ := by
    simpa only [setIntegral_univ] using setIntegral_condExp hm hC MeasurableSet.univ
  have hQE : (∫ ω, (μ[Q | m]) ω ∂μ)=∫ ω, Q ω ∂μ := by
    simpa only [setIntegral_univ] using setIntegral_condExp hm hQ MeasurableSet.univ
  have hint := integral_mono_ae integrable_condExp hright hcond
  rw [hCE,integral_sub hAS (integrable_condExp.const_mul (2*η)),
    integral_add hA hσ,integral_const_mul,hQE] at hint
  exact hint

end
end Tournament.Upper.ExponentialWeights
