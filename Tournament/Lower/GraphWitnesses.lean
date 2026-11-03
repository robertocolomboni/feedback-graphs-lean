module

public import Tournament.Graphs.FewObservers
public import Tournament.Graphs.Structure
public import Tournament.Lower.Main

@[expose] public section

namespace Tournament.Lower

open MeasureTheory Model.MeasurableGame
open scoped Classical
noncomputable section

variable {ι : Type*}

theorem exists_unrevealing_pair (E : ι → ι → Prop) (hE : ¬StronglyRevealing E) :
    ∃ a b, a≠b ∧ ¬(E a a ∧ E a b) ∧ ¬(E b b ∧ E b a) := by
  simpa only [StronglyRevealing,not_forall,Classical.not_imp,not_or,exists_prop] using hE

theorem sparse_pair (E : ι → ι → Prop) (a b : ι)
    (ha : ¬(E a a ∧ E a b)) (hb : ¬(E b b ∧ E b a)) :
    SparseMembers E {a,b} := by
  intro c hc
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [observed,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases (show c=a ∨ c=b by simpa only [Finset.mem_insert,Finset.mem_singleton] using hc) with rfl | rfl
  · rcases hu.1 with rfl | rfl <;> rcases hv.1 with rfl | rfl <;> tauto
  · rcases hu.1 with rfl | rfl <;> rcases hv.1 with rfl | rfl <;> tauto

theorem sparse_of_no_distinct_edges (E : ι → ι → Prop) (S : Finset ι)
    (hNo : ∀ u∈S, ∀ v∈S, u≠v → ¬E u v) : SparseMembers E S := by
  intro a ha
  have hOnly (v : ι) (hv : v∈observed E S a) : v=a := by
    by_contra hne
    exact hNo a ha v (Finset.mem_filter.mp hv).1 (Ne.symm hne) (Finset.mem_filter.mp hv).2
  exact Finset.card_le_one.mpr (fun u hu v hv ↦ (hOnly u hu).trans (hOnly v hv).symm)

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]
variable {Seed : Type*} [MeasurableSpace Seed]

theorem pair_lower_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ) (hT : 2≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hE : ¬StronglyRevealing E) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      (T:ℝ)^((2:ℝ)/3)/(256*Dyadic.upsilon T)≤deterministicExpectedRegret T ν π E loss := by
  obtain ⟨a,b,hab,ha,hb⟩ := exists_unrevealing_pair E hE
  have hCard : ({a,b}:Finset ι).card=2 := Finset.card_pair hab
  have hObs (c : ι) : ((observed E {a,b} c).card:ℝ)≤2 := by
    have h := (Finset.card_le_card (Finset.filter_subset (E c) ({a,b}:Finset ι)))
    rw [hCard] at h
    exact_mod_cast h
  obtain ⟨loss,hBound,hReg⟩ := lower_bound ν hT π E (sparse_pair E a b ha hb)
    (by omega) 2 (by norm_num) hObs
  have hTR : (2:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  refine ⟨loss,hBound,?_⟩
  simpa only [hCard,Nat.cast_ofNat,min_eq_left hTR,div_self (by norm_num : (2:ℝ)≠0),Real.one_rpow,mul_one] using hReg

end
end Tournament.Lower
