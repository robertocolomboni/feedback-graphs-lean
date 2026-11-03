module

public import Tournament.Lower.FairSigns

@[expose] public section

namespace Tournament.Lower.FairSigns

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval

noncomputable section

theorem coin_flip_preserving : MeasurePreserving Bool.not coinLaw coinLaw := by
  refine ⟨Measurable.of_discrete,?_⟩
  rw [coinLaw,map_bernoulliMeasure]
  have hh : unitInterval.symm half=half := by
    apply Subtype.ext
    norm_num [half]
  simp only [Bool.not_true,Bool.not_false,bernoulliMeasure_def,hh]
  exact add_comm _ _

def flip {T : ℕ} (t : Fin T) (ω : Space T) (u : Fin T) : Bool :=
  if u=t then !(ω u) else ω u

theorem flip_involutive {T : ℕ} (t : Fin T) : Function.Involutive (flip t) := by
  intro ω
  funext u
  by_cases hu : u=t <;> simp [flip,hu]

theorem flip_measurable {T : ℕ} (t : Fin T) : Measurable (flip t) := by
  apply Measurable.of_eval
  intro u
  by_cases hu : u=t
  · simp only [flip,ite_eq_left hu]
    exact (Measurable.of_discrete (f := Bool.not)).comp (measurable_pi_apply u)
  · simp only [flip,ite_eq_right hu]
    exact measurable_pi_apply u

theorem flip_preserving (T : ℕ) (t : Fin T) : MeasurePreserving (flip t) (law T) (law T) := by
  apply measurePreserving_pi (fun _ : Fin T ↦ coinLaw) (fun _ : Fin T ↦ coinLaw)
    (f := fun u b ↦ if u=t then !b else b)
  intro u
  by_cases hu : u=t
  · simp only [ite_eq_left hu]
    exact coin_flip_preserving
  · simp only [ite_eq_right hu]
    exact MeasurePreserving.id coinLaw

theorem sign_flip {T : ℕ} (t : Fin T) (ω : Space T) : sign t (flip t ω)= -sign t ω := by
  simp only [sign,flip]
  cases h : ω t <;> norm_num [value]

theorem sign_flip_other {T : ℕ} (t u : Fin T) (htu : u≠t) (ω : Space T) :
    sign u (flip t ω)=sign u ω := by
  simp only [sign,flip,ite_eq_right htu]

end
end Tournament.Lower.FairSigns
