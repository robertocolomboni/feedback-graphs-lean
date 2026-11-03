module

public import Tournament.Upper.PivotCells
public import Tournament.Upper.PivotLogCount

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def selectedIndicator (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U) (i : ι) : ℝ :=
  if i∈pivotList F n U run then 1 else 0

def ownedIndicator (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U) (s i : ι) : ℝ :=
  if owner F n U run i=some s then 1 else 0

def selectedProb (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (i : ι) : ℝ :=
  (law F v hv n U).mean (fun run ↦ selectedIndicator F n U run i)

def ownedProb (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (s i : ι) : ℝ :=
  (law F v hv n U).mean (fun run ↦ ownedIndicator F n U run s i)

theorem selectedProb_nonneg (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (i : ι) : 0≤selectedProb F v hv n U i := by
  apply ProbabilityVector.mean_nonneg
  intro run
  unfold selectedIndicator
  split <;> norm_num

theorem selectedProb_le_one (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (i : ι) : selectedProb F v hv n U i≤1 := by
  calc
    _ ≤ (law F v hv n U).mean (fun _ ↦ 1) := by
      apply ProbabilityVector.mean_mono
      intro run
      unfold selectedIndicator
      split <;> norm_num
    _ = _ := ProbabilityVector.mean_const _ _

theorem ownedProb_nonneg (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (s i : ι) : 0≤ownedProb F v hv n U s i := by
  apply ProbabilityVector.mean_nonneg
  intro run
  unfold ownedIndicator
  split <;> norm_num

theorem ownedProb_le_selectedProb (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (s i : ι) : ownedProb F v hv n U s i≤selectedProb F v hv n U s := by
  apply ProbabilityVector.mean_mono
  intro run
  unfold ownedIndicator selectedIndicator
  by_cases h : owner F n U run i=some s
  · simp only [ite_eq_left h,ite_eq_left (owner_selected F n U run i s h)]
    exact le_refl _
  · simp only [ite_eq_right h]
    split <;> norm_num

omit [Fintype ι] in
theorem selectedIndicator_outside (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (i : ι) (hi : i∉U) : selectedIndicator F n U run i=0 := by
  exact ite_eq_right (fun h ↦ hi (pivotList_mem F n U run i h))

omit [Fintype ι] in
theorem ownedIndicator_outside (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (run : Run F n U)
    (s i : ι) (hi : i∉U) : ownedIndicator F n U run s i=0 := by
  unfold ownedIndicator
  rw [owner_outside F n U run i hi]
  simp

omit [Fintype ι] in
theorem selectedIndicator_succ (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (hU : U.Nonempty)
    (run : Run F (n+1) U) (i : ι) :
    selectedIndicator F (n+1) U run i=
      (if i=(uncons F n U hU run).1.val then 1 else 0)+
        selectedIndicator F n (survivors F U (uncons F n U hU run).1.val) (uncons F n U hU run).2 i := by
  by_cases hi : i=(uncons F n U hU run).1.val
  · have hout : i∉survivors F U (uncons F n U hU run).1.val := by
      rw [hi]
      exact pivot_not_survivor F U _
    rw [selectedIndicator_outside F n _ _ i hout]
    simp [selectedIndicator,pivotList,hU,hi]
  · simp [selectedIndicator,pivotList,hU,hi]

omit [Fintype ι] in
theorem ownedIndicator_succ (F : ι → ι → Prop) (n : ℕ) (U : Finset ι) (hU : U.Nonempty)
    (run : Run F (n+1) U) (s i : ι) :
    ownedIndicator F (n+1) U run s i=
      (if s=(uncons F n U hU run).1.val ∧ i∈cell F U (uncons F n U hU run).1.val then 1 else 0)+
        ownedIndicator F n (survivors F U (uncons F n U hU run).1.val) (uncons F n U hU run).2 s i := by
  by_cases hc : i∈cell F U (uncons F n U hU run).1.val
  · have hout : i∉survivors F U (uncons F n U hU run).1.val := by
      intro hi
      exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hc).2
    rw [ownedIndicator_outside F n _ _ s i hout]
    simp [ownedIndicator,owner,hU,hc,eq_comm]
  · simp [ownedIndicator,owner,hU,hc]

theorem selectedProb_succ (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty) (i : ι) :
    selectedProb F v hv (n+1) U i=(pivotLaw v hv U hU).mean (fun t ↦ if i=t.val then 1 else 0)+
      (pivotLaw v hv U hU).mean (fun t ↦ selectedProb F v hv n (survivors F U t.val) i) := by
  unfold selectedProb
  have hfun := funext (fun run ↦ selectedIndicator_succ F n U hU run i)
  rw [hfun,ProbabilityVector.mean_add]
  congr 1
  · rw [law_uncons_mean F v hv n U hU (fun t ↦ if i=t.1.val then 1 else 0)]
    congr 1
    funext t
    exact ProbabilityVector.mean_const (law F v hv n (survivors F U t.val)) (if i=t.val then 1 else 0)
  · exact law_uncons_mean F v hv n U hU (fun t ↦ selectedIndicator F n (survivors F U t.1.val) t.2 i)

theorem ownedProb_succ (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty) (s i : ι) :
    ownedProb F v hv (n+1) U s i=(pivotLaw v hv U hU).mean
        (fun t ↦ if s=t.val ∧ i∈cell F U t.val then 1 else 0)+
      (pivotLaw v hv U hU).mean (fun t ↦ ownedProb F v hv n (survivors F U t.val) s i) := by
  unfold ownedProb
  have hfun := funext (fun run ↦ ownedIndicator_succ F n U hU run s i)
  rw [hfun,ProbabilityVector.mean_add]
  congr 1
  · rw [law_uncons_mean F v hv n U hU (fun t ↦ if s=t.1.val ∧ i∈cell F U t.1.val then 1 else 0)]
    congr 1
    funext t
    exact ProbabilityVector.mean_const (law F v hv n (survivors F U t.val))
      (if s=t.val ∧ i∈cell F U t.val then 1 else 0)
  · exact law_uncons_mean F v hv n U hU (fun t ↦ ownedIndicator F n (survivors F U t.1.val) t.2 s i)

theorem first_selection_probability (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (U : Finset ι) (hU : U.Nonempty) (i : ι) :
    (pivotLaw v hv U hU).mean (fun t ↦ if i=t.val then 1 else 0)=
      if i∈U then v i/mass v U else 0 := by
  rw [pivotLaw_mean v hv U hU (fun t ↦ if i=t then 1 else 0)]
  simp only [mul_ite,mul_one,mul_zero]
  split <;> simp_all

theorem first_ownership_probability (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (U : Finset ι) (hU : U.Nonempty) (s i : ι) :
    (pivotLaw v hv U hU).mean (fun t ↦ if s=t.val ∧ i∈cell F U t.val then 1 else 0)=
      if s∈U ∧ i∈cell F U s then v s/mass v U else 0 := by
  have hfun : (fun t : {j // j∈U} ↦ if s=t.val ∧ i∈cell F U t.val then (1:ℝ) else 0)=
      (fun t ↦ if i∈cell F U s then (if s=t.val then 1 else 0) else 0) := by
    funext t
    by_cases hs : s=t.val <;> simp [hs]
  rw [hfun]
  by_cases hc : i∈cell F U s
  · simp only [hc,ite_true,and_true]
    exact first_selection_probability v hv U hU s
  · simp [hc]

theorem first_load_le (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (U : Finset ι) (hU : U.Nonempty) (s i : ι) :
    v i*(pivotLaw v hv U hU).mean (fun t ↦ if s=t.val ∧ i∈cell F U t.val then 1 else 0)≤
      v s*(pivotLaw v hv U hU).mean (fun t ↦ if i=t.val then 1 else 0) := by
  rw [first_ownership_probability,first_selection_probability]
  by_cases h : s∈U ∧ i∈cell F U s
  · rw [ite_eq_left h,ite_eq_left (Finset.mem_filter.mp h.2).1]
    exact le_of_eq (by ring)
  · rw [ite_eq_right h]
    simp only [mul_zero]
    apply mul_nonneg (v.nonneg s)
    split
    · exact div_nonneg (v.nonneg i) (mass_nonneg v U)
    · norm_num

theorem ownedProb_balanced (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (s i : ι) :
    v i*ownedProb F v hv n U s i≤v s*selectedProb F v hv n U i := by
  induction n generalizing U with
  | zero => simp [ownedProb,selectedProb,ownedIndicator,selectedIndicator,owner,pivotList]
  | succ n ih =>
    by_cases hU : U.Nonempty
    · rw [ownedProb_succ F v hv n U hU,selectedProb_succ F v hv n U hU]
      have hhead := first_load_le F v hv U hU s i
      have htail : v i*(pivotLaw v hv U hU).mean (fun t ↦ ownedProb F v hv n (survivors F U t.val) s i)≤
          v s*(pivotLaw v hv U hU).mean (fun t ↦ selectedProb F v hv n (survivors F U t.val) i) := by
        rw [← ProbabilityVector.mean_const_mul,← ProbabilityVector.mean_const_mul]
        exact ProbabilityVector.mean_mono _ (fun t ↦ ih (survivors F U t.val))
      nlinarith
    · simp [ownedProb,selectedProb,ownedIndicator,selectedIndicator,owner,pivotList,hU]

theorem selectedProb_sum (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) : (∑ i, selectedProb F v hv n U i)=expectedCount F v hv n U := by
  unfold selectedProb expectedCount
  rw [← ProbabilityVector.mean_sum]
  congr 1
  funext run
  calc
    _ = ((pivotList F n U run).toFinset.card:ℝ) := by
      simp [selectedIndicator,← List.mem_toFinset]
    _ = _ := by rw [List.toFinset_card_of_nodup (pivotList_nodup F n U run)]

end
end Tournament.Upper.RootedPivots
