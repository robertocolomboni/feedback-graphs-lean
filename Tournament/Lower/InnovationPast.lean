module

public import Tournament.Lower.GaussianInnovations
public import Tournament.Lower.AugmentedExecution

@[expose] public section

namespace Tournament.Lower.GaussianProduct

open scoped Classical

noncomputable section

theorem walk_eraseRow {C : Type*} {T : ℕ} (t : Fin T) (s : ℕ) (hst : s≤t.val)
    (c : C) (ω : Space T C) : walk c s (eraseRow t ω)=walk c s ω := by
  unfold walk Dyadic.finiteWalk
  apply Finset.sum_congr rfl
  intro j hj
  have hanc := Dyadic.mem_ancestors_bounds s (j.val+1) (Finset.mem_filter.mp hj).2
  have hne : j≠t := by
    intro h
    have he := congrArg Fin.val h
    omega
  simp only [increment,eraseRow,ite_eq_right hne]

end
end Tournament.Lower.GaussianProduct

namespace Tournament.Lower

open Model.MeasurableGame
open scoped Classical

noncomputable section

variable {ι Seed : Type*} {S : Finset ι} {T : ℕ}

def eraseInnovation (t : Fin T) (ω : WalkSign.Space T (Coordinate S)) : WalkSign.Space T (Coordinate S) :=
  (ω.1,GaussianProduct.eraseRow t ω.2)

theorem past_walk_erase (t : Fin T) (s : ℕ) (hst : s≤t.val) (c : Coordinate S)
    (ω : WalkSign.Space T (Coordinate S)) :
    WalkSign.walk c s (eraseInnovation t ω)=WalkSign.walk c s ω :=
  GaussianProduct.walk_eraseRow t s hst c ω.2

theorem augmentedSignal_erase (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (s : ℕ) (hst : s<t.val) (ω : WalkSign.Space T (Coordinate S)) (a : ι) :
    augmentedSignal E θ j s (eraseInnovation t ω,a)=augmentedSignal E θ j s (ω,a) := by
  have hs : s<T := hst.trans t.isLt
  have hx : (fun c ↦ WalkSign.walk c (s+1) (eraseInnovation t ω))=
      (fun c ↦ WalkSign.walk c (s+1) ω) := by
    funext c
    exact past_walk_erase t (s+1) (by omega) c ω
  have hsign : WalkSign.sign ⟨s,hs⟩ (eraseInnovation t ω)=WalkSign.sign ⟨s,hs⟩ ω := rfl
  simp only [augmentedSignal,dite_eq_left hs]
  rw [hsign,hx]

variable [MeasurableSpace ι] [MeasurableSpace Seed]

theorem augmentedHistory_erase (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (n : ℕ) (hnt : n≤t.val) (seed : Seed)
    (ω : WalkSign.Space T (Coordinate S)) :
    augmentedHistory π E θ j n (seed,eraseInnovation t ω)=augmentedHistory π E θ j n (seed,ω) := by
  apply runSensor_equal_of_past_signals π (augmentedDecoder E S) (augmentedSignal E θ j) n
    (seed,eraseInnovation t ω) (seed,ω) rfl
  intro s hs a
  exact augmentedSignal_erase E θ j t s (by omega) ω a

theorem augmentedAction_erase (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (seed : Seed) (ω : WalkSign.Space T (Coordinate S)) :
    sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) t.val (seed,eraseInnovation t ω)=
      sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) t.val (seed,ω) := by
  have hh := augmentedHistory_erase π E θ j t t.val le_rfl seed ω
  change π.choose t.val (seed,decodeHistory (augmentedDecoder E S) t.val
    (augmentedHistory π E θ j t.val (seed,eraseInnovation t ω)))=_
  rw [hh]
  rfl

end
end Tournament.Lower
