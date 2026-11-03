module

public import Tournament.Model.MeasurableLearner
public import Tournament.Lower.ClippingExperiment
public import Tournament.Lower.SignFlips

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι : Type*} {S : Finset ι} {T : ℕ}

theorem sampledRawLoss_measurable (θ : ℝ) (j : Coordinate S) (t : Fin T) (v : S) :
    Measurable (sampledRawLoss θ j t v) := by
  have h0 := WalkSign.walk_measurable T (none : Coordinate S) (t.val+1)
  have hv := WalkSign.walk_measurable T (some v) (t.val+1)
  have hs := WalkSign.sign_measurable (C := Coordinate S) T t
  exact ((measurable_const.add h0).add (hs.mul hv)).sub measurable_const

def sampledLoss (θ : ℝ) (j : Coordinate S) (s : ℕ) (ω : WalkSign.Space T (Coordinate S)) : ι → ℝ :=
  if hs : s<T then
    environmentLoss θ j (WalkSign.sign ⟨s,hs⟩ ω) (fun c ↦ WalkSign.walk c (s+1) ω)
  else 0

theorem sampledLoss_measurable (θ : ℝ) (j : Coordinate S) (s : ℕ) :
    Measurable (sampledLoss (T := T) θ j s) := by
  by_cases hs : s<T
  · apply Measurable.of_eval
    intro a
    by_cases ha : a∈S
    · simp only [sampledLoss,dite_eq_left hs,environmentLoss,dite_eq_left ha]
      exact clip_continuous.measurable.comp (sampledRawLoss_measurable θ j ⟨s,hs⟩ ⟨a,ha⟩)
    · simp only [sampledLoss,dite_eq_left hs,environmentLoss,dite_eq_right ha]
      exact measurable_const
  · unfold sampledLoss
    simp only [dite_eq_right hs]
    exact measurable_const

theorem sampledLoss_bounds (θ : ℝ) (j : Coordinate S) (s : ℕ)
    (ω : WalkSign.Space T (Coordinate S)) (a : ι) :
    0≤sampledLoss θ j s ω a ∧ sampledLoss θ j s ω a≤1 := by
  by_cases hs : s<T
  · simp only [sampledLoss,dite_eq_left hs]
    exact environmentLoss_bounds θ j _ _ a
  · simp only [sampledLoss,dite_eq_right hs,Pi.zero_apply]
    norm_num

theorem sampledLoss_member (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (ω : WalkSign.Space T (Coordinate S)) (v : S) :
    sampledLoss θ j t.val ω v=clip (sampledRawLoss θ j t v ω) := by
  simp only [sampledLoss,dite_eq_left t.isLt,environmentLoss,dite_eq_left v.property,sampledRawLoss]

def flipSample (t : Fin T) (ω : WalkSign.Space T (Coordinate S)) : WalkSign.Space T (Coordinate S) :=
  (FairSigns.flip t ω.1,ω.2)

theorem flipSample_preserving (t : Fin T) :
    MeasurePreserving (flipSample (S := S) t) (environmentLaw S T) (environmentLaw S T) :=
  (FairSigns.flip_preserving T t).prod (MeasurePreserving.id (GaussianProduct.law T (incrementVariance T)))

theorem flipSample_sign (t : Fin T) (ω : WalkSign.Space T (Coordinate S)) :
    WalkSign.sign t (flipSample t ω)= -WalkSign.sign t ω := FairSigns.sign_flip t ω.1

theorem sampledLoss_flip (θ : ℝ) (j : Coordinate S) (t : Fin T) (s : ℕ) (hst : s<t.val)
    (ω : WalkSign.Space T (Coordinate S)) : sampledLoss θ j s (flipSample t ω)=sampledLoss θ j s ω := by
  have hs : s<T := hst.trans t.isLt
  have hne : (⟨s,hs⟩ : Fin T)≠t := by
    intro h
    have hv := congrArg Fin.val h
    change s=t.val at hv
    omega
  have hsign := FairSigns.sign_flip_other t ⟨s,hs⟩ hne ω.1
  simp only [sampledLoss,dite_eq_left hs,WalkSign.sign,flipSample,hsign]
  rfl

variable {Seed : Type*} [MeasurableSpace ι] [MeasurableSpace Seed]

def learnerAction (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (s : ℕ) : Seed × WalkSign.Space T (Coordinate S) → ι :=
  action π E (sampledLoss θ j) s

theorem learnerAction_measurable [DiscreteMeasurableSpace ι] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (s : ℕ) :
    Measurable (learnerAction (T := T) π E θ j s) :=
  action_measurable π E (sampledLoss θ j) (sampledLoss_measurable θ j) s

theorem learnerAction_flip (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (seed : Seed) (ω : WalkSign.Space T (Coordinate S)) :
    learnerAction π E θ j t.val (seed,flipSample t ω)=learnerAction π E θ j t.val (seed,ω) := by
  symm
  apply action_equal_of_past_feedback π E (sampledLoss θ j) (sampledLoss θ j)
    t.val (seed,ω) (seed,flipSample t ω) rfl
  intro s hs
  rw [sampledLoss_flip θ j t s hs ω]

end
end Tournament.Lower
