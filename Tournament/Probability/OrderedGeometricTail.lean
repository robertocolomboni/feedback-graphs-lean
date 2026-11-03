module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Tournament.Probability

open scoped Classical BigOperators
noncomputable section

variable {α : Type*} [LinearOrder α]

def inclusiveRank (A : Finset α) (t : α) : ℕ := (A.filter (fun u ↦ u≤t)).card

theorem inclusiveRank_strict {A : Finset α} {t u : α} (hu : u∈A) (htu : t<u) :
    inclusiveRank A t<inclusiveRank A u := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.trans htu.le⟩
  · intro hEq
    have huR : u∈A.filter (fun v ↦ v≤u) := Finset.mem_filter.mpr ⟨hu,le_rfl⟩
    have huL : u∈A.filter (fun v ↦ v≤t) := by rw [hEq]; exact huR
    exact (not_le_of_gt htu) (Finset.mem_filter.mp huL).2

theorem inclusiveRank_injOn (A : Finset α) : Set.InjOn (inclusiveRank A) (A : Set α) := by
  intro t ht u hu hEq
  rcases lt_trichotomy t u with h | h | h
  · have hRank := inclusiveRank_strict hu h
    omega
  · exact h
  · have hRank := inclusiveRank_strict ht h
    omega

theorem inclusiveRank_bounds (A : Finset α) (t : α) (ht : t∈A) :
    1≤inclusiveRank A t ∧ inclusiveRank A t≤A.card := by
  constructor
  · exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,le_rfl⟩⟩
  · exact Finset.card_filter_le _ _

theorem ordered_geometric_tail (A : Finset α) (r : ℝ) (hr : 0≤r) (hr1 : r<1) :
    (∑ t∈A, r^(inclusiveRank A t))≤r/(1-r) := by
  have hSub : A.image (inclusiveRank A) ⊆ Finset.Ico 1 (A.card+1) := by
    intro j hj
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
    have h := inclusiveRank_bounds A t ht
    exact Finset.mem_Ico.mpr ⟨h.1,by omega⟩
  calc
    _ = ∑ j∈A.image (inclusiveRank A), r^j := (Finset.sum_image (inclusiveRank_injOn A)).symm
    _ ≤ ∑ j∈Finset.Ico 1 (A.card+1), r^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun j _ _ ↦ pow_nonneg hr j)
    _ ≤ _ := by simpa only [pow_one] using geom_sum_Ico_le_of_lt_one hr hr1 (m := 1) (n := A.card+1)

end
end Tournament.Probability
