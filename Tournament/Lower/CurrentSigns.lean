module

public import Tournament.Lower.InnovationPast

@[expose] public section

namespace Tournament.Lower.FairSigns

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

noncomputable section

def otherIndices {T : ℕ} (t : Fin T) : Finset (Fin T) := Finset.univ.erase t

def otherSnapshot {T : ℕ} (t : Fin T) (ω : Space T) : otherIndices t → Bool := fun u ↦ ω u

def restoreOther {T : ℕ} (t : Fin T) (x : otherIndices t → Bool) : Space T :=
  fun u ↦ if hu : u≠t then x ⟨u,by simp [otherIndices,hu]⟩ else false

theorem otherSnapshot_measurable {T : ℕ} (t : Fin T) : Measurable (otherSnapshot t) :=
  Measurable.of_eval (fun u ↦ measurable_pi_apply u.val)

theorem restoreOther_measurable {T : ℕ} (t : Fin T) : Measurable (restoreOther t) := by
  apply Measurable.of_eval
  intro u
  by_cases hu : u≠t
  · simp only [restoreOther,dite_eq_left hu]
    exact measurable_pi_apply _
  · simp only [restoreOther,dite_eq_right hu]
    exact measurable_const

theorem other_current_independent (T : ℕ) (t : Fin T) :
    IndepFun (otherSnapshot t) (fun ω : Space T ↦ ω t) (law T) := by
  have hall : iIndepFun (fun u : Fin T ↦ fun ω : Space T ↦ ω u) (law T) :=
    iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  have hdis : Disjoint (otherIndices t) {t} := by simp [otherIndices]
  have h := hall.indepFun_finset (otherIndices t) {t} hdis (fun u ↦ measurable_pi_apply u)
  exact h.comp (φ := id) (ψ := fun x : ({t} : Finset (Fin T)) → Bool ↦ x ⟨t,by simp⟩)
    measurable_id (measurable_pi_apply _)

variable {C Seed : Type*} [Fintype C] [MeasurableSpace Seed]

theorem current_private_independent (ν : Measure Seed) [IsProbabilityMeasure ν]
    (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    IndepFun (fun p : Seed × WalkSign.Space T C ↦ (p.1,(p.2.2,otherSnapshot t p.2.1)))
      (fun p ↦ p.2.1 t) (ν.prod (WalkSign.law T v)) := by
  have h := Tournament.Probability.independent_private_extension (law T) (GaussianProduct.law (C := C) T v)
    (otherSnapshot t) (fun ω : Space T ↦ ω t) (otherSnapshot_measurable t) (measurable_pi_apply t)
    (other_current_independent T t)
  have hswap := (Measure.measurePreserving_swap (μ := law T) (ν := GaussianProduct.law (C := C) T v)).hasLaw
  have hwalk := Tournament.Probability.independent_pullback Prod.swap hswap
    (fun p : GaussianProduct.Space T C × Space T ↦ (p.1,otherSnapshot t p.2)) (fun p ↦ p.2 t)
    (measurable_fst.prodMk ((otherSnapshot_measurable t).comp measurable_snd))
    ((measurable_pi_apply t).comp measurable_snd) h
  exact Tournament.Probability.independent_private_extension (WalkSign.law (C := C) T v) ν
    (fun ω ↦ (ω.2,otherSnapshot t ω.1)) (fun ω ↦ ω.1 t)
    (measurable_snd.prodMk ((otherSnapshot_measurable t).comp measurable_fst))
    ((measurable_pi_apply t).comp measurable_fst) hwalk

end
end Tournament.Lower.FairSigns

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def eraseCurrentCoin (t : Fin T) (ω : WalkSign.Space T (Coordinate S)) : WalkSign.Space T (Coordinate S) :=
  (FairSigns.restoreOther t (FairSigns.otherSnapshot t ω.1),ω.2)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem past_sign_eraseCurrentCoin (t : Fin T) (s : Fin T) (hst : s.val<t.val)
    (ω : WalkSign.Space T (Coordinate S)) :
    WalkSign.sign s (eraseCurrentCoin t ω)=WalkSign.sign s ω := by
  have hne : s≠t := by intro h; have hv := congrArg Fin.val h; omega
  simp [WalkSign.sign,FairSigns.sign,eraseCurrentCoin,FairSigns.restoreOther,hne,FairSigns.otherSnapshot]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem augmentedSignal_eraseCurrentCoin (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (s : ℕ) (hst : s<t.val) (ω : WalkSign.Space T (Coordinate S)) (a : ι) :
    augmentedSignal E θ j s (eraseCurrentCoin t ω,a)=augmentedSignal E θ j s (ω,a) := by
  have hs : s<T := hst.trans t.isLt
  simp only [augmentedSignal,dite_eq_left hs]
  rw [past_sign_eraseCurrentCoin t ⟨s,hs⟩ hst ω]
  rfl

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem augmentedHistory_eraseCurrentCoin (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (seed : Seed) (ω : WalkSign.Space T (Coordinate S)) :
    augmentedHistory π E θ j t.val (seed,eraseCurrentCoin t ω)=augmentedHistory π E θ j t.val (seed,ω) := by
  apply runSensor_equal_of_past_signals
  · rfl
  · intro s hs a
    exact augmentedSignal_eraseCurrentCoin E θ j t s hs ω a

def pastState (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ)
    (p : Seed × WalkSign.Space T (Coordinate S)) : Seed × SensorHistory ι (AugmentedSignal S) n :=
  (p.1,augmentedHistory π E θ j n p)

theorem pastState_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ) :
    Measurable (pastState (T := T) π E θ j n) :=
  measurable_fst.prodMk (augmentedHistory_measurable π E θ j n)

def pastStateSignFactor (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (r : Seed × (GaussianProduct.Space T (Coordinate S) × (FairSigns.otherIndices t → Bool))) :
    Seed × SensorHistory ι (AugmentedSignal S) t.val :=
  pastState π E θ j t.val (r.1,(FairSigns.restoreOther t r.2.2,r.2.1))

theorem pastStateSignFactor_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) : Measurable (pastStateSignFactor π E θ j t) :=
  (pastState_measurable π E θ j t.val).comp
    (measurable_fst.prodMk (((FairSigns.restoreOther_measurable t).comp measurable_snd.snd).prodMk measurable_snd.fst))

theorem pastState_current_sign_independent (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    IndepFun (pastState π E θ j t.val) (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.sign t p.2)
      (privateLaw ν S T) := by
  have hi := FairSigns.current_private_independent (C := Coordinate S) ν T (incrementVariance T) t
  have h := hi.comp (φ := pastStateSignFactor π E θ j t) (ψ := FairSigns.value)
    (pastStateSignFactor_measurable π E θ j t) FairSigns.value_measurable
  have heq : (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
      pastStateSignFactor π E θ j t (p.1,(p.2.2,FairSigns.otherSnapshot t p.2.1)))=
      pastState π E θ j t.val := by
    funext p
    change (p.1,augmentedHistory π E θ j t.val (p.1,eraseCurrentCoin t p.2))=(p.1,augmentedHistory π E θ j t.val p)
    rw [augmentedHistory_eraseCurrentCoin]
  change IndepFun (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
    pastStateSignFactor π E θ j t (p.1,(p.2.2,FairSigns.otherSnapshot t p.2.1)))
    (fun p ↦ WalkSign.sign t p.2) (privateLaw ν S T) at h
  rw [heq] at h
  exact h

end
end Tournament.Lower
