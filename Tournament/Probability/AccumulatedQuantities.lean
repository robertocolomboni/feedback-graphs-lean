module

public import Tournament.Probability.FilteredExponential

@[expose] public section

namespace Tournament.FilteredMoments

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem accumulated_quantities_ae (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (b v : ℝ) (hB : 0<b+v)
    (hbound : ∀ t, t<N → ∀ᵐ ω ∂μ, 0≤Y t ω ∧ Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v)
    (θ : ℝ) (hθ : 0≤θ) (hθB : θ<1/(b+v)) :
    (∫ ω, Real.exp (θ*(∑ t ∈ Finset.range N, Y t ω)) ∂μ)≤
      1+θ*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)/(1-θ*(b+v)) := by
  let : MeasurableSpace Ω := mΩ
  by_cases hN : N=0
  · subst N
    simp
  have hN0 : 0<N := Nat.pos_of_ne_zero hN
  have hb : 0≤b := by
    obtain ⟨ω,hω⟩ := (hbound 0 hN0).exists
    exact hω.1.trans hω.2
  let Good := fun ω ↦ ∀ t, t<N → 0≤Y t ω ∧ Y t ω≤b
  have hgood : ∀ᵐ ω ∂μ, Good ω := by
    rw [ae_all_iff]
    intro t
    by_cases ht : t<N
    · filter_upwards [hbound t ht] with ω hω
      exact fun _ ↦ hω
    · exact Eventually.of_forall (fun _ ht' ↦ False.elim (ht ht'))
  let Z := fun t ω ↦ if Good ω then Y t ω else 0
  have heq (t : ℕ) : Z t=ᵐ[μ] Y t := hgood.mono (fun _ hω ↦ ite_eq_left hω)
  have hZ (t : ℕ) (ht : t<N) : AEStronglyMeasurable[history (t+1)] (Z t) μ :=
    (hY t ht).congr (heq t).symm
  have hZbound (t : ℕ) (ht : t<N) (ω : Ω) : 0≤Z t ω ∧ Z t ω≤b := by
    by_cases hω : Good ω
    · simpa only [Z,ite_eq_left hω] using hω t ht
    · simp only [Z,ite_eq_right hω]
      exact ⟨le_refl _,hb⟩
  have htail (t : ℕ) : (fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Z u ω else 0)=ᵐ[μ]
      (fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0) := by
    filter_upwards [hgood] with ω hω
    apply Finset.sum_congr rfl
    intro u _
    simp only [Z,ite_eq_left hω]
  have hZfuture (t : ℕ) (ht : t<N) : μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Z u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v :=
    (condExp_congr_ae (htail t)).trans_le (hfuture t ht)
  have htotal : (fun ω ↦ ∑ t ∈ Finset.range N, Z t ω)=ᵐ[μ]
      (fun ω ↦ ∑ t ∈ Finset.range N, Y t ω) := by
    filter_upwards [hgood] with ω hω
    apply Finset.sum_congr rfl
    intro t _
    simp only [Z,ite_eq_left hω]
  have hexp : (fun ω ↦ Real.exp (θ*(∑ t ∈ Finset.range N, Z t ω)))=ᵐ[μ]
      (fun ω ↦ Real.exp (θ*(∑ t ∈ Finset.range N, Y t ω))) :=
    htotal.mono (fun _ hω ↦ congrArg (fun q : ℝ ↦ Real.exp (θ*q)) hω)
  have h := accumulated_quantities μ history hmono hglobal Z N hZ b v hB hZbound hZfuture θ hθ hθB
  rw [integral_congr_ae hexp,integral_congr_ae htotal] at h
  exact h

theorem accumulated_quantities_finite_horizon (N : ℕ)
    (history : Fin (N+1) → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ (t : ℕ) (ht : t<N), AEStronglyMeasurable[history ⟨t+1,by omega⟩] (Y t) μ)
    (b v : ℝ) (hB : 0<b+v)
    (hbound : ∀ t, t<N → ∀ᵐ ω ∂μ, 0≤Y t ω ∧ Y t ω≤b)
    (hfuture : ∀ (t : ℕ) (ht : t<N),
      μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
        history ⟨t+1,by omega⟩] ≤ᵐ[μ] fun _ ↦ v)
    (θ : ℝ) (hθ : 0≤θ) (hθB : θ<1/(b+v)) :
    (∫ ω, Real.exp (θ*(∑ t ∈ Finset.range N, Y t ω)) ∂μ)≤
      1+θ*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)/(1-θ*(b+v)) := by
  let extended := fun t : ℕ ↦ history ⟨min t N,by omega⟩
  have hmono' : Monotone extended := by
    intro s t hst
    apply hmono
    change min s N≤min t N
    omega
  have hglobal' (t : ℕ) : extended t≤mΩ := hglobal _
  have hext (t : ℕ) (ht : t≤N) : extended t=history ⟨t,by omega⟩ := by
    apply congrArg history
    apply Fin.ext
    exact min_eq_left ht
  have hY' (t : ℕ) (ht : t<N) : AEStronglyMeasurable[extended (t+1)] (Y t) μ := by
    rw [hext (t+1) (by omega)]
    exact hY t ht
  have hfuture' (t : ℕ) (ht : t<N) :
      μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 | extended (t+1)] ≤ᵐ[μ] fun _ ↦ v := by
    rw [hext (t+1) (by omega)]
    exact hfuture t ht
  exact accumulated_quantities_ae μ extended hmono' hglobal' Y N hY' b v hB hbound hfuture' θ hθ hθB

end
end Tournament.FilteredMoments
