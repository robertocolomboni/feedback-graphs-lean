module

public import Tournament.Upper.RootedPivots

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem pivotList_mem (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (i : ι) (hi : i∈pivotList F n U run) : i∈U := by
  induction n generalizing U with
  | zero => simp only [pivotList,List.not_mem_nil] at hi
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [pivotList,dite_eq_left hU,List.mem_cons] at hi
      rcases hi with hi | hi
      · exact hi ▸ (uncons F n U hU run).1.property
      · exact survivors_subset F U _ (ih _ (uncons F n U hU run).2 hi)
    · simp only [pivotList,dite_eq_right hU,List.not_mem_nil] at hi

omit [Fintype ι] in
theorem pivotList_nodup (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U) :
    (pivotList F n U run).Nodup := by
  induction n generalizing U with
  | zero => simp only [pivotList,List.nodup_nil]
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [pivotList,dite_eq_left hU,List.nodup_cons]
      constructor
      · intro hi
        have hm := pivotList_mem F n _ (uncons F n U hU run).2 _ hi
        exact pivot_not_survivor F U _ hm
      · exact ih _ (uncons F n U hU run).2
    · simp only [pivotList,dite_eq_right hU,List.nodup_nil]

omit [Fintype ι] in
theorem pivots_point_to_earlier (F : ι → ι → Prop) (hF : IsTournament F)
    (n : ℕ) (U : Finset ι) (run : Run F n U) :
    (pivotList F n U run).Pairwise (fun earlier later ↦ F later earlier) := by
  induction n generalizing U with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [pivotList,dite_eq_left hU,List.pairwise_cons]
      constructor
      · intro i hi
        have hm := pivotList_mem F n _ (uncons F n U hU run).2 i hi
        exact ((survivor_iff F hF U _ i).mp hm).2.2
      · exact ih _ (uncons F n U hU run).2
    · simp only [pivotList,dite_eq_right hU]
      exact List.Pairwise.nil

def owner (F : ι → ι → Prop) : (n : ℕ) → (U : Finset ι) → Run F n U → ι → Option ι
  | 0, _, _, _ => none
  | n+1, U, run, i => if hU : U.Nonempty then
      let chosen := uncons F n U hU run
      if i∈cell F U chosen.1.val then some chosen.1.val
      else owner F n (survivors F U chosen.1.val) chosen.2 i
    else none

omit [Fintype ι] in
theorem owner_outside (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (i : ι) (hi : i∉U) : owner F n U run i=none := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih =>
    by_cases hU : U.Nonempty
    · have hcell : i∉cell F U (uncons F n U hU run).1.val := fun h ↦ hi (Finset.mem_filter.mp h).1
      simp only [owner,dite_eq_left hU,ite_eq_right hcell]
      exact ih _ (uncons F n U hU run).2 (fun h ↦ hi (survivors_subset F U _ h))
    · simp only [owner,dite_eq_right hU]

omit [Fintype ι] in
theorem owner_selected (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (i s : ι) (hs : owner F n U run i=some s) : s∈pivotList F n U run := by
  induction n generalizing U with
  | zero => cases hs
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [owner,dite_eq_left hU] at hs
      simp only [pivotList,dite_eq_left hU,List.mem_cons]
      split at hs
      · exact Or.inl (Option.some.inj hs).symm
      · exact Or.inr (ih _ (uncons F n U hU run).2 hs)
    · simp only [owner,dite_eq_right hU] at hs
      cases hs

omit [Fintype ι] in
theorem owner_compares_target (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (i s : ι) (hs : owner F n U run i=some s) : InClosedNeighborhood F s i := by
  induction n generalizing U with
  | zero => cases hs
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [owner,dite_eq_left hU] at hs
      split at hs
      · have heq : (uncons F n U hU run).1.val=s := Option.some.inj hs
        have hclosed := (Finset.mem_filter.mp ‹i∈cell F U (uncons F n U hU run).1.val›).2
        exact heq ▸ hclosed
      · exact ih _ (uncons F n U hU run).2 hs
    · simp only [owner,dite_eq_right hU] at hs
      cases hs

omit [Fintype ι] in
theorem owner_covers (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (hn : U.card≤n)
    (run : Run F n U) (i : ι) (hi : i∈U) : ∃ s, owner F n U run i=some s := by
  induction n generalizing U with
  | zero =>
    have hU : U=∅ := Finset.card_eq_zero.mp (by omega)
    simp [hU] at hi
  | succ n ih =>
    have hU : U.Nonempty := ⟨i,hi⟩
    simp only [owner,dite_eq_left hU]
    by_cases hc : i∈cell F U (uncons F n U hU run).1.val
    · exact ⟨_,ite_eq_left hc⟩
    · rw [ite_eq_right hc]
      have his : i∈survivors F U (uncons F n U hU run).1.val := by
        refine Finset.mem_filter.mpr ⟨hi,?_⟩
        intro hclosed
        exact hc (Finset.mem_filter.mpr ⟨hi,hclosed⟩)
      have hcard := survivors_card_lt F U (uncons F n U hU run).1.val (uncons F n U hU run).1.property
      exact ih _ (by omega) (uncons F n U hU run).2 his

omit [Fintype ι] in
theorem owner_compares_root (F : ι → ι → Prop) (hF : IsTournament F)
    (n : ℕ) (U : Finset ι) (run : Run F n U) (i s r : ι)
    (hs : owner F n U run i=some s) (hr : (pivotList F n U run).head?=some r) :
    InClosedNeighborhood F s r := by
  have hselected := owner_selected F n U run i s hs
  have hpair := pivots_point_to_earlier F hF n U run
  cases hlist : pivotList F n U run with
  | nil =>
    rw [hlist] at hr
    cases hr
  | cons a rest =>
    rw [hlist] at hr hselected hpair
    have har : a=r := Option.some.inj hr
    subst a
    rcases List.mem_cons.mp hselected with heq | hmem
    · exact Or.inl heq.symm
    · exact Or.inr ((List.pairwise_cons.mp hpair).1 s hmem)

end
end Tournament.Upper.RootedPivots
