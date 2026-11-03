module

public import Tournament.Probability.EntropyVariational

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped NNReal ENNReal Classical

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def likelihoodDeficit (μ ν : Measure Ω) (ω : Ω) : ℝ := max (1-(μ.rnDeriv ν ω).toReal) 0

def acTotalVariation (μ ν : Measure Ω) : ℝ := ∫ ω, likelihoodDeficit μ ν ω ∂ν

def deficitSet (μ ν : Measure Ω) : Set Ω := {ω | (μ.rnDeriv ν ω).toReal<1}

theorem deficitSet_measurable (μ ν : Measure Ω) : MeasurableSet (deficitSet μ ν) :=
  measurableSet_lt (Measure.measurable_rnDeriv μ ν).ennreal_toReal measurable_const

variable {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem likelihoodDeficit_integrable : Integrable (likelihoodDeficit μ ν) ν :=
  ((integrable_const (1:ℝ)).sub Measure.integrable_toReal_rnDeriv).sup (integrable_const 0)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem acTotalVariation_nonneg : 0≤acTotalVariation μ ν :=
  integral_nonneg (fun _ ↦ le_max_right _ _)

theorem acTotalVariation_le_one : acTotalVariation μ ν≤1 := by
  calc
    _ ≤ ∫ _ : Ω, (1:ℝ) ∂ν := by
      apply integral_mono likelihoodDeficit_integrable (integrable_const 1)
      intro ω
      exact max_le (by have h := ENNReal.toReal_nonneg (a := μ.rnDeriv ν ω); linarith) (by norm_num)
    _ = _ := by simp

theorem acTotalVariation_attained (hac : μ≪ν) :
    acTotalVariation μ ν=ν.real (deficitSet μ ν)-μ.real (deficitSet μ ν) := by
  have heq : likelihoodDeficit μ ν=(deficitSet μ ν).indicator (fun ω ↦ 1-(μ.rnDeriv ν ω).toReal) := by
    funext ω
    by_cases hω : ω∈deficitSet μ ν
    · rw [Set.indicator_of_mem hω]
      exact max_eq_left (by have h := hω; change (μ.rnDeriv ν ω).toReal<1 at h; linarith)
    · rw [Set.indicator_of_notMem hω]
      exact max_eq_right (by have h := hω; change ¬(μ.rnDeriv ν ω).toReal<1 at h; linarith)
  unfold acTotalVariation
  rw [heq,integral_indicator (deficitSet_measurable μ ν),
    integral_sub (integrable_const (1:ℝ)) (Measure.integrable_toReal_rnDeriv.restrict),
    setIntegral_const,Measure.setIntegral_toReal_rnDeriv hac]
  simp only [smul_eq_mul,mul_one]

theorem expectation_sub_le_totalVariation (hac : μ≪ν) (f : Ω → ℝ) (hf : AEMeasurable f ν)
    (T : ℝ) (hbound : ∀ᵐ ω ∂ν, f ω∈Set.Icc 0 T) :
    (∫ ω, f ω ∂ν)-(∫ ω, f ω ∂μ)≤T*acTotalVariation μ ν := by
  have hfν := Integrable.of_mem_Icc 0 T hf hbound
  have hfμ := Integrable.of_mem_Icc 0 T (hf.mono_ac hac) (hac.ae_le hbound)
  have hweighted := (integrable_toReal_rnDeriv_mul_iff hac).mpr hfμ
  have hmono := integral_mono_ae (hfν.sub hweighted) (likelihoodDeficit_integrable.const_mul T) (by
    filter_upwards [hbound] with ω hω
    change f ω-(μ.rnDeriv ν ω).toReal*f ω≤T*max (1-(μ.rnDeriv ν ω).toReal) 0
    by_cases hr : 0≤1-(μ.rnDeriv ν ω).toReal
    · rw [max_eq_left hr]
      nlinarith [mul_le_mul_of_nonneg_left hω.2 hr]
    · rw [max_eq_right (by linarith)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) hω.1])
  change (∫ ω, f ω-(μ.rnDeriv ν ω).toReal*f ω ∂ν)≤
    ∫ ω, T*likelihoodDeficit μ ν ω ∂ν at hmono
  rw [integral_sub hfν hweighted,integral_toReal_rnDeriv_mul hac,integral_const_mul] at hmono
  exact hmono

theorem abs_expectation_sub_le_totalVariation (hac : μ≪ν) (f : Ω → ℝ) (hf : AEMeasurable f ν)
    (T : ℝ) (hbound : ∀ᵐ ω ∂ν, f ω∈Set.Icc 0 T) :
    |(∫ ω, f ω ∂μ)-(∫ ω, f ω ∂ν)|≤T*acTotalVariation μ ν := by
  have hupper := expectation_sub_le_totalVariation hac f hf T hbound
  have hbound' : ∀ᵐ ω ∂ν, T-f ω∈Set.Icc 0 T :=
    hbound.mono (fun ω hω ↦ ⟨by linarith [hω.2],by linarith [hω.1]⟩)
  have hlower := expectation_sub_le_totalVariation hac (fun ω ↦ T-f ω) (aemeasurable_const.sub hf) T hbound'
  have hfν := Integrable.of_mem_Icc 0 T hf hbound
  have hfμ := Integrable.of_mem_Icc 0 T (hf.mono_ac hac) (hac.ae_le hbound)
  rw [integral_sub (integrable_const T) hfμ,integral_sub (integrable_const T) hfν] at hlower
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hlower
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem acTotalVariation_controls_events (hac : μ≪ν) (s : Set Ω) (hs : MeasurableSet s) :
    |μ.real s-ν.real s|≤acTotalVariation μ ν := by
  let f : Ω → ℝ := s.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hb : ∀ᵐ ω ∂ν, f ω∈Set.Icc 0 1 := Filter.Eventually.of_forall (fun ω ↦ by
    by_cases hω : ω∈s <;> simp [f,hω])
  have h := abs_expectation_sub_le_totalVariation hac f hf.aemeasurable 1 hb
  simpa only [f,integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one,one_mul] using h

theorem pinsker (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) :
    acTotalVariation μ ν≤sqrt ((klDiv μ ν).toReal/2) := by
  let s := deficitSet μ ν
  have hs : MeasurableSet s := deficitSet_measurable μ ν
  let f : Ω → ℝ := s.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hb : ∀ᵐ ω ∂ν, f ω∈Set.Icc 0 1 := Filter.Eventually.of_forall (fun ω ↦ by
    by_cases hω : ω∈s <;> simp [f,hω])
  have h := bounded_observable_pinsker hac hKL f hf.aemeasurable 0 1 (by norm_num) hb
  simp only [f,integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one,sub_zero,one_mul] at h
  rw [acTotalVariation_attained hac]
  have hneg := (neg_le_abs (μ.real s-ν.real s)).trans h
  linarith

end
end Tournament.Probability
