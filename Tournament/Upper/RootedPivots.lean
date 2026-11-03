module

public import Tournament.Upper.BalancedEstimator
public import Tournament.Probability.Restarts
public import Tournament.Probability.FiniteReindex

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

universe u
variable {ι : Type u} [Fintype ι]

def mass (v : ProbabilityVector ι) (U : Finset ι) : ℝ := ∑ i ∈ U, v i

theorem mass_nonneg (v : ProbabilityVector ι) (U : Finset ι) : 0≤mass v U :=
  Finset.sum_nonneg (fun i _ ↦ v.nonneg i)

theorem mass_pos (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) (hU : U.Nonempty) :
    0<mass v U := Finset.sum_pos (fun i _ ↦ hv i) hU

@[simp] theorem mass_empty (v : ProbabilityVector ι) : mass v ∅=0 := by simp [mass]

@[simp] theorem mass_univ (v : ProbabilityVector ι) : mass v Finset.univ=1 := v.sum_eq_one

theorem mass_le_one (v : ProbabilityVector ι) (U : Finset ι) : mass v U≤1 := by
  calc
    _ ≤ ∑ i, v i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun i _ _ ↦ v.nonneg i)
    _ = 1 := v.sum_eq_one

def pivotLaw (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) (hU : U.Nonempty) :
    ProbabilityVector {i // i∈U} where
  weight s := v s.val/mass v U
  nonneg s := div_nonneg (v.nonneg s.val) (le_of_lt (mass_pos v hv U hU))
  sum_eq_one := by
    rw [← Finset.sum_div,Finset.sum_coe_sort]
    exact div_self (ne_of_gt (mass_pos v hv U hU))

theorem pivotLaw_mean (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) (hU : U.Nonempty)
    (f : ι → ℝ) :
    (pivotLaw v hv U hU).mean (fun s ↦ f s.val)=
      (∑ s ∈ U, v s*f s)/mass v U := by
  change (∑ s : {i // i∈U}, (v s.val/mass v U)*f s.val)=_
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,Finset.sum_coe_sort U (fun s ↦ v s*f s)]

def cell (F : ι → ι → Prop) (U : Finset ι) (s : ι) : Finset ι :=
  U.filter (fun i ↦ InClosedNeighborhood F s i)

def survivors (F : ι → ι → Prop) (U : Finset ι) (s : ι) : Finset ι :=
  U.filter (fun i ↦ ¬InClosedNeighborhood F s i)

omit [Fintype ι] in
theorem survivors_subset (F : ι → ι → Prop) (U : Finset ι) (s : ι) : survivors F U s⊆U :=
  Finset.filter_subset _ _

omit [Fintype ι] in
theorem pivot_not_survivor (F : ι → ι → Prop) (U : Finset ι) (s : ι) : s∉survivors F U s := by
  simp [survivors,InClosedNeighborhood]

omit [Fintype ι] in
theorem survivors_card_lt (F : ι → ι → Prop) (U : Finset ι) (s : ι) (hs : s∈U) :
    (survivors F U s).card<U.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨survivors_subset F U s,?_⟩
  intro heq
  have hnot := pivot_not_survivor F U s
  rw [heq] at hnot
  exact hnot hs

omit [Fintype ι] in
theorem cell_union_survivors (F : ι → ι → Prop) (U : Finset ι) (s : ι) :
    cell F U s ∪ survivors F U s=U := by
  ext i
  simp only [cell,survivors,Finset.mem_union,Finset.mem_filter]
  tauto

omit [Fintype ι] in
theorem cell_disjoint_survivors (F : ι → ι → Prop) (U : Finset ι) (s : ι) :
    Disjoint (cell F U s) (survivors F U s) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2

omit [Fintype ι] in
theorem survivor_iff (F : ι → ι → Prop) (hF : IsTournament F) (U : Finset ι) (s i : ι) :
    i∈survivors F U s ↔ i∈U ∧ i≠s ∧ F i s := by
  simp only [survivors,Finset.mem_filter,InClosedNeighborhood,not_or]
  constructor
  · rintro ⟨hi,his,hnsi⟩
    refine ⟨hi,his,?_⟩
    rcases (hF i s his).1 with his' | hsi
    · exact his'
    · exact False.elim (hnsi hsi)
  · rintro ⟨hi,his,his'⟩
    refine ⟨hi,his,?_⟩
    intro hsi
    exact (hF i s his).2 ⟨his',hsi⟩

def Run (F : ι → ι → Prop) : ℕ → Finset ι → Type u
  | 0, _ => ULift.{u} Unit
  | n+1, U => if U.Nonempty then Σ s : {i // i∈U}, Run F n (survivors F U s.val) else ULift.{u} Unit

instance runFintype (F : ι → ι → Prop) : (n : ℕ) → (U : Finset ι) → Fintype (Run F n U)
  | 0, _ => inferInstanceAs (Fintype (ULift Unit))
  | n+1, U => by
    unfold Run
    split
    · letI : ∀ s : {i // i∈U}, Fintype (Run F n (survivors F U s.val)) := fun s ↦ runFintype F n _
      exact inferInstance
    · exact inferInstance

def uncons (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (hU : U.Nonempty) :
    Run F (n+1) U ≃ (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) :=
  Equiv.cast (by simp only [Run,ite_eq_left hU])

def emptyEquiv (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (hU : ¬U.Nonempty) :
    Run F (n+1) U ≃ ULift.{u} Unit := Equiv.cast (by simp only [Run,ite_eq_right hU])

def terminalLaw : ProbabilityVector (ULift.{u} Unit) :=
  ⟨fun _ ↦ 1,fun _ ↦ zero_le_one,by simp⟩

def law (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (n : ℕ) → (U : Finset ι) → ProbabilityVector (Run F n U)
  | 0, _ => terminalLaw
  | n+1, U => if hU : U.Nonempty then
      ((pivotLaw v hv U hU).sigmaJoint (fun s ↦ law F v hv n (survivors F U s.val))).reindex (uncons F n U hU).symm
    else terminalLaw.reindex (emptyEquiv F n U hU).symm

def remainder (F : ι → ι → Prop) : (n : ℕ) → (U : Finset ι) → Run F n U → Finset ι
  | 0, U, _ => U
  | n+1, U, run => if hU : U.Nonempty then
      let chosen := uncons F n U hU run
      remainder F n (survivors F U chosen.1.val) chosen.2
    else ∅

def pivotList (F : ι → ι → Prop) : (n : ℕ) → (U : Finset ι) → Run F n U → List ι
  | 0, _, _ => []
  | n+1, U, run => if hU : U.Nonempty then
      let chosen := uncons F n U hU run
      chosen.1.val :: pivotList F n (survivors F U chosen.1.val) chosen.2
    else []

theorem law_step (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty)
    (f : (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) → ℝ) :
    let μ : ProbabilityVector (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) :=
      (pivotLaw v hv U hU).sigmaJoint (fun s ↦ law F v hv n (survivors F U s.val))
    μ.mean f=(pivotLaw v hv U hU).mean (fun s ↦ (law F v hv n (survivors F U s.val)).mean (fun rest ↦ f ⟨s,rest⟩)) :=
  ProbabilityVector.sigmaJoint_mean _ _ _

theorem law_uncons_mean (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty)
    (g : (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) → ℝ) :
    (law F v hv (n+1) U).mean (fun run ↦ g (uncons F n U hU run))=
      (pivotLaw v hv U hU).mean (fun s ↦
        (law F v hv n (survivors F U s.val)).mean (fun rest ↦ g ⟨s,rest⟩)) := by
  rw [law,dite_eq_left hU,ProbabilityVector.reindex_mean]
  have hfun : (fun chosen ↦ g (uncons F n U hU ((uncons F n U hU).symm chosen)))=g := by
    funext chosen
    exact congrArg g ((uncons F n U hU).apply_symm_apply chosen)
  change ((pivotLaw v hv U hU).sigmaJoint (fun s ↦ law F v hv n (survivors F U s.val))).mean
    (fun chosen ↦ g (uncons F n U hU ((uncons F n U hU).symm chosen)))=_
  rw [hfun]
  exact ProbabilityVector.sigmaJoint_mean (pivotLaw v hv U hU)
    (fun s ↦ law F v hv n (survivors F U s.val)) g

omit [Fintype ι] in
theorem remainder_subset (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U) :
    remainder F n U run⊆U := by
  induction n generalizing U with
  | zero => exact Finset.Subset.refl U
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [remainder,dite_eq_left hU]
      exact Finset.Subset.trans (ih _ (uncons F n U hU run).2) (survivors_subset F U (uncons F n U hU run).1.val)
    · simp only [remainder,dite_eq_right hU]
      exact Finset.empty_subset U

omit [Fintype ι] in
theorem remainder_empty_of_card_le (F : ι → ι → Prop) (n : ℕ) (U : Finset ι)
    (hn : U.card≤n) (run : Run F n U) : remainder F n U run=∅ := by
  induction n generalizing U with
  | zero =>
    have hU : U=∅ := Finset.card_eq_zero.mp (by omega)
    exact hU
  | succ n ih =>
    by_cases hU : U.Nonempty
    · simp only [remainder,dite_eq_left hU]
      have hcard := survivors_card_lt F U (uncons F n U hU run).1.val (uncons F n U hU run).1.property
      exact ih _ (by omega) (uncons F n U hU run).2
    · simp only [remainder,dite_eq_right hU]

end
end Tournament.Upper.RootedPivots
