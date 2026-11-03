module

public import Tournament.Graphs.Structure
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Tournament

open scoped Classical

noncomputable section

variable {ι : Type*}

def ObservingSet (E : ι → ι → Prop) (D : Finset ι) : Prop :=
  ∀ i, ∃ s ∈ D, E s i

def Observable (E : ι → ι → Prop) : Prop := ∀ i, ∃ s, E s i

def observingSources (E : ι → ι → Prop) (D : Finset ι) (i : ι) : Finset ι :=
  D.filter (fun s ↦ E s i)

theorem observingSources_nonempty {E : ι → ι → Prop} {D : Finset ι} (hD : ObservingSet E D) (i : ι) :
    (observingSources E D i).Nonempty := by
  rcases hD i with ⟨s,hs,hsi⟩
  exact ⟨s,Finset.mem_filter.mpr ⟨hs,hsi⟩⟩

theorem observingSet_nonempty [Nonempty ι] {E : ι → ι → Prop} {D : Finset ι} (hD : ObservingSet E D) :
    D.Nonempty := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  rcases hD i with ⟨s,hs,_⟩
  exact ⟨s,hs⟩

theorem observingSet_implies_observable {E : ι → ι → Prop} {D : Finset ι} (hD : ObservingSet E D) :
    Observable E := fun i ↦ by rcases hD i with ⟨s,_,h⟩; exact ⟨s,h⟩

theorem observable_iff_observing_univ [Fintype ι] (E : ι → ι → Prop) :
    Observable E ↔ ObservingSet E Finset.univ := by
  constructor
  · intro h i
    rcases h i with ⟨s,hs⟩
    exact ⟨s,Finset.mem_univ s,hs⟩
  · exact observingSet_implies_observable

end
end Tournament
