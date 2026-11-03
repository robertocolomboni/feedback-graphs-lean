module

public import Tournament.Graphs.Observing
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Tournament

open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def observedMembers (E : ι → ι → Prop) (W : Finset ι) (a : ι) : Finset ι :=
  W.filter (fun v ↦ E a v)

theorem exists_observing_card (E : ι → ι → Prop) (hE : Observable E) :
    ∃ n : ℕ, ∃ D : Finset ι, ObservingSet E D ∧ D.card=n :=
  ⟨Fintype.card ι,Finset.univ,(observable_iff_observing_univ E).mp hE,Finset.card_univ⟩

def dominationNumber (E : ι → ι → Prop) (hE : Observable E) : ℕ :=
  Nat.find (exists_observing_card E hE)

theorem exists_minimum_observing (E : ι → ι → Prop) (hE : Observable E) :
    ∃ D : Finset ι, ObservingSet E D ∧ D.card=dominationNumber E hE :=
  Nat.find_spec (exists_observing_card E hE)

theorem dominationNumber_le (E : ι → ι → Prop) (hE : Observable E) (D : Finset ι) (hD : ObservingSet E D) :
    dominationNumber E hE≤D.card := Nat.find_min' (exists_observing_card E hE) ⟨D,hD,rfl⟩

theorem dominationNumber_le_card (E : ι → ι → Prop) (hE : Observable E) :
    dominationNumber E hE≤Fintype.card ι := by
  simpa only [Finset.card_univ] using dominationNumber_le E hE Finset.univ ((observable_iff_observing_univ E).mp hE)

theorem dominationNumber_pos [Nonempty ι] (E : ι → ι → Prop) (hE : Observable E) :
    0<dominationNumber E hE := by
  obtain ⟨D,hD,hcard⟩ := exists_minimum_observing E hE
  rw [← hcard]
  exact Finset.card_pos.mpr (observingSet_nonempty hD)

theorem no_small_observing (E : ι → ι → Prop) (hE : Observable E) (D : Finset ι)
    (hD : D.card<dominationNumber E hE) : ¬ ObservingSet E D := by
  intro hObs
  exact (not_lt_of_ge (dominationNumber_le E hE D hObs)) hD

end
end Tournament
