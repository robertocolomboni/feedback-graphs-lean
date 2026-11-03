module

public import Tournament.Probability.AccumulatedQuantities
public import Tournament.Probability.AccumulatedMoments
public import Tournament.Probability.FiniteConditionalMeasure

@[expose] public section

namespace Tournament.FiniteConditional

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω S : Type*} [Fintype Ω] [Fintype S]
variable [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [mS : MeasurableSpace S] [MeasurableSingletonClass S]

theorem condExp_le_of_meanLE (μ : ProbabilityVector Ω) (info : Ω → S)
    (f : Ω → ℝ) (c : ℝ) (hf : MeanLE μ info f c) :
    μ.toMeasure[f | MeasurableSpace.comap info mS] ≤ᵐ[μ.toMeasure] fun _ ↦ c := by
  have hsingle (ω : Ω) : μ ω ≤ fiberMass μ info (info ω) := by
    have h := Finset.single_le_sum
      (f := fun ω' ↦ if info ω'=info ω then μ ω' else 0)
      (fun ω' _ ↦ by split <;> simp_all [μ.nonneg]) (Finset.mem_univ ω)
    simpa only [ite_true,fiberMass] using h
  have hzero (s : S) (hs : fiberMass μ info s=0) : fiberSum μ info f s=0 := by
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : info ω=s
    · have hz : μ ω=0 := by
        have hh := hsingle ω
        rw [hω,hs] at hh
        exact le_antisymm hh (μ.nonneg ω)
      simp only [hω,ite_true,hz,zero_mul]
    · simp only [hω,ite_false]
  let H := fun s ↦ fiberSum μ info f s / fiberMass μ info s
  have hidentity (s : S) : fiberSum μ info f s=H s*fiberMass μ info s := by
    by_cases hs : fiberMass μ info s=0
    · simp only [H,hs,hzero s hs,div_zero,mul_zero]
    · exact (div_mul_cancel₀ _ hs).symm
  have hce := condExp_of_fiber_identity μ info f H hidentity
  have hle : (fun ω ↦ H (info ω)) ≤ᵐ[μ.toMeasure] fun _ ↦ c := by
    change ∀ᵐ ω ∂μ.toMeasure, H (info ω)≤c
    rw [μ.ae_toMeasure_iff]
    intro ω hω
    exact (div_le_iff₀ (hω.trans_le (hsingle ω))).mpr (hf (info ω))
  exact hce.trans_le hle

omit mΩ [MeasurableSingletonClass Ω] in
theorem measurable_of_dependsOn (info : Ω → S) (f : Ω → ℝ)
    (hf : DependsOn info f) : Measurable[MeasurableSpace.comap info mS] f := by
  have h := (measurable_of_finite (fiberValue info f)).comp (comap_measurable info)
  change Measurable[MeasurableSpace.comap info mS]
    (fun ω ↦ fiberValue info f (info ω)) at h
  have heq : (fun ω ↦ fiberValue info f (info ω))=f :=
    funext (fiberValue_on info f hf)
  rwa [heq] at h

end
end Tournament.FiniteConditional

namespace Tournament.AccumulatedMoments

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem accumulated_exponential_mean_le_from_general
    {S : ℕ → Type*} [∀ t, Fintype (S t)]
    (μ : ProbabilityVector Ω) (info : (t : ℕ) → Ω → S t)
    (hinfo : IncreasingInformation info) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY : ∀ t, t<n → FiniteConditional.DependsOn (info (t+1)) (Y t))
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (b v : ℝ) (hB : 0 < b+v)
    (hbound : ∀ t, t<n → ∀ ω, Y t ω ≤ b)
    (hfuture : ∀ t, t<n → FiniteConditional.MeanLE μ (info (t+1))
      (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) v)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθB : θ*(b+v) < 1) :
    μ.mean (fun ω ↦ Real.exp (θ*(∑ t ∈ Finset.range n, Y t ω))) ≤
      1+θ*μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω)/(1-θ*(b+v)) := by
  let : MeasurableSpace Ω := ⊤
  let : ∀ t, MeasurableSpace (S t) := fun _ ↦ ⊤
  let history : Fin (n+1) → MeasurableSpace Ω :=
    fun t ↦ MeasurableSpace.comap (info t.val) ⊤
  have hmono : Monotone history := by
    intro s t hst A hA
    obtain ⟨B,_hB,hBA⟩ := MeasurableSpace.measurableSet_comap.mp hA
    subst A
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨{z | ∃ ω, info t.val ω=z ∧ info s.val ω∈B}, by trivial, ?_⟩
    ext ω
    constructor
    · rintro ⟨ω',hω',hB'⟩
      change info s.val ω∈B
      rwa [hinfo s.val t.val hst ω' ω hω'] at hB'
    · intro hω
      exact ⟨ω,rfl,hω⟩
  have hadapt (t : ℕ) (ht : t<n) :
      AEStronglyMeasurable[history ⟨t+1,by omega⟩] (Y t) μ.toMeasure :=
    (FiniteConditional.measurable_of_dependsOn (info (t+1)) (Y t) (hY t ht)).stronglyMeasurable.aestronglyMeasurable
  have hcond (t : ℕ) (ht : t<n) :
      μ.toMeasure[fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0 |
        history ⟨t+1,by omega⟩] ≤ᵐ[μ.toMeasure] fun _ ↦ v :=
    FiniteConditional.condExp_le_of_meanLE μ (info (t+1)) _ v (hfuture t ht)
  have h := FilteredMoments.accumulated_quantities_finite_horizon μ.toMeasure n history
    hmono (fun _ ↦ le_top) Y hadapt b v hB
    (fun t ht ↦ Eventually.of_forall (fun ω ↦ ⟨hY0 t ω,hbound t ht ω⟩))
    hcond θ hθ ((lt_div_iff₀ hB).mpr hθB)
  simpa only [μ.integral_toMeasure] using h

end
end Tournament.AccumulatedMoments
