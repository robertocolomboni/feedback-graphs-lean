module

public import Tournament.Lower.FairExpertEnvironment
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

namespace Tournament.Lower.FairExperts

open MeasureTheory Model MeasurableGame
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 800000

variable {ι Seed : Type*} [MeasurableSpace ι] [MeasurableSpace Seed] {T : ℕ}

theorem fresh_coefficient_mean_zero (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι)
    (t : Fin T) (seed : Seed) :
    (∫ ω, FairSigns.sign t ω*coefficient a b (learnerAction π E a b t.val (seed,ω)) ∂FairSigns.law T)=0 := by
  let F : FairSigns.Space T → ℝ := fun ω ↦
    FairSigns.sign t ω*coefficient a b (learnerAction π E a b t.val (seed,ω))
  have hSame := (FairSigns.flip_preserving T t).hasLaw.integral_comp
    (Measurable.of_discrete (f := F)).aestronglyMeasurable
  simp only [Function.comp_apply] at hSame
  have hFlip (ω : FairSigns.Space T) : F (FairSigns.flip t ω)= -F ω := by
    dsimp [F]
    rw [FairSigns.sign_flip,learnerAction_flip]
    ring
  have hNeg : (∫ ω, F (FairSigns.flip t ω) ∂FairSigns.law T)=-(∫ ω, F ω ∂FairSigns.law T) := by
    calc
      _ = ∫ ω, -F ω ∂FairSigns.law T := integral_congr_ae (Filter.Eventually.of_forall hFlip)
      _ = _ := integral_neg _
  change (∫ ω, F ω ∂FairSigns.law T)=0
  linarith

theorem expected_selected_loss (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι)
    (t : Fin T) (seed : Seed) :
    (1:ℝ)/2≤∫ ω, loss a b t.val ω (learnerAction π E a b t.val (seed,ω)) ∂FairSigns.law T := by
  have h := integral_mono (μ := FairSigns.law T) Integrable.of_finite Integrable.of_finite
    (fun ω ↦ selected_loss_lower a b (learnerAction π E a b t.val (seed,ω)) t.val ω)
  simp only [signAt,dite_eq_left t.isLt] at h
  rw [integral_add Integrable.of_finite Integrable.of_finite] at h
  simp only [integral_div,integral_const,probReal_univ,one_smul] at h
  rw [fresh_coefficient_mean_zero π E a b t seed] at h
  simpa only [zero_div,add_zero] using h

variable [Fintype ι] [Nonempty ι]

def regretAt (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι)
    (seed : Seed) (ω : FairSigns.Space T) : ℝ :=
  pathRegret T (fun t ↦ loss a b t ω) (fun t ↦ learnerAction π E a b t (seed,ω))

omit [Fintype ι] [Nonempty ι] in
theorem expected_played_seed (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (seed : Seed) :
    (T:ℝ)/2≤∫ ω, accumulatedLoss T (fun t ↦ loss a b t ω)
      (fun t ↦ learnerAction π E a b t (seed,ω)) ∂FairSigns.law T := by
  unfold accumulatedLoss
  rw [integral_finsetSum (Finset.range T) (fun _ _ ↦ Integrable.of_finite)]
  calc
    _ = ∑ _t∈Finset.range T, (1:ℝ)/2 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum (fun t ht ↦ expected_selected_loss π E a b ⟨t,Finset.mem_range.mp ht⟩ seed)

theorem expected_regret_seed (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (hab : a≠b) (seed : Seed) :
    (∫ ω, |∑ t : Fin T, FairSigns.sign t ω| ∂FairSigns.law T)/2≤
      ∫ ω, regretAt π E a b seed ω ∂FairSigns.law T := by
  have hPoint (ω : FairSigns.Space T) :
      accumulatedLoss T (fun t ↦ loss a b t ω) (fun t ↦ learnerAction π E a b t (seed,ω))-
        (T:ℝ)/2+|∑ t : Fin T, FairSigns.sign t ω|/2≤regretAt π E a b seed ω := by
    have hBest := bestFixedLoss_upper a b hab ω
    have hSwitch : (0:ℝ)≤(switchCount T (fun t ↦ learnerAction π E a b t (seed,ω)):ℝ) := by positivity
    unfold regretAt pathRegret
    linarith
  have h := integral_mono (μ := FairSigns.law T) Integrable.of_finite Integrable.of_finite hPoint
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite] at h
  simp only [integral_div,integral_const,probReal_univ,one_smul] at h
  have hPlayed := expected_played_seed (T := T) π E a b seed
  linarith

theorem regretAt_section (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι)
    (seed : Seed) (ω : FairSigns.Space T) :
    regretAt π E a b seed ω=deterministicPathRegret T π E (fun t ↦ loss a b t ω) seed := by
  unfold regretAt deterministicPathRegret
  congr 1
  funext t
  exact (action_section π E (loss a b) t seed ω).symm

variable [DiscreteMeasurableSpace ι]

theorem regretAt_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) :
    Integrable (fun p : Seed × FairSigns.Space T ↦ regretAt π E a b p.1 p.2)
      (ν.prod (FairSigns.law T)) := by
  exact pathRegret_integrable (ν.prod (FairSigns.law T)) T
    (fun t (p : Seed × FairSigns.Space T) ↦ loss a b t p.2)
    (fun t i ↦ (Measurable.of_discrete (f := fun ω ↦ loss (T := T) a b t ω i)).comp measurable_snd)
    (fun t p i ↦ loss_bounds a b t p.2 i) (learnerAction π E a b)
    (fun t ↦ action_measurable π E (loss a b) (loss_measurable a b) t)

theorem exists_oblivious_loss (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (hab : a≠b) :
    ∃ L : ℕ → ι → ℝ, BoundedSequence L ∧
      (∫ ω, |∑ t : Fin T, FairSigns.sign t ω| ∂FairSigns.law T)/2≤deterministicExpectedRegret T ν π E L := by
  have hI := regretAt_integrable (T := T) ν π E a b
  have h := integral_mono (μ := ν)
    (integrable_const ((∫ ω, |∑ t : Fin T, FairSigns.sign t ω| ∂FairSigns.law T)/2))
    hI.integral_prod_left (expected_regret_seed π E a b hab)
  simp only [integral_const,probReal_univ,one_smul] at h
  have hSections : (fun ω : FairSigns.Space T ↦ ∫ seed, regretAt π E a b seed ω ∂ν)=
      fun ω ↦ deterministicExpectedRegret T ν π E (fun t ↦ loss a b t ω) := by
    funext ω
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun seed ↦ regretAt_section π E a b seed ω)
  rw [← integral_prod _ hI,integral_prod_symm _ hI,hSections] at h
  have hOuter := hI.integral_prod_right
  rw [hSections] at hOuter
  obtain ⟨ω,hω⟩ := exists_integral_le hOuter
  exact ⟨(fun t ↦ loss a b t ω),(fun t i ↦ loss_bounds a b t ω i),h.trans hω⟩

theorem lower_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ) (hT : 1≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hK : 2≤Fintype.card ι) :
    ∃ L : ℕ → ι → ℝ, BoundedSequence L ∧ Real.sqrt (T:ℝ)/4≤deterministicExpectedRegret T ν π E L := by
  obtain ⟨a,_,b,_,hab⟩ := Finset.one_lt_card.mp
    (show 1<(Finset.univ : Finset ι).card by rw [Finset.card_univ]; omega)
  obtain ⟨L,hL,hReg⟩ := exists_oblivious_loss (T := T) ν π E a b hab
  exact ⟨L,hL,(FairSigns.half_absolute_sum_lower T hT).trans hReg⟩

end
end Tournament.Lower.FairExperts

namespace Tournament.Lower.FairExperts

open Model.MeasurableGame

universe u v
variable {ι : Type u} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]

theorem minimax_lower_bound (T : ℕ) (hT : 1≤T) (E : ι → ι → Prop) (hK : 2≤Fintype.card ι) :
    Real.sqrt (T:ℝ)/4≤minimax.{u,v} T E := by
  apply le_minimax
  intro σ
  let := σ.seedSpace
  let := σ.probability
  obtain ⟨L,hL,hReg⟩ := lower_bound σ.law T hT σ.learner E hK
  exact ⟨L,hL,hReg⟩

end Tournament.Lower.FairExperts
