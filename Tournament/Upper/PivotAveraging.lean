module

public import Tournament.Upper.PivotSelection

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev FullRun (F : ι → ι → Prop) := Run F (Fintype.card ι+1) Finset.univ

def fullLaw (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) : ProbabilityVector (FullRun F) :=
  law F v hv (Fintype.card ι+1) Finset.univ

theorem fullSet_nonempty (v : ProbabilityVector ι) : (Finset.univ:Finset ι).Nonempty := by
  have : Nonempty ι := v.nonempty
  exact Finset.univ_nonempty

def fullRoot (F : ι → ι → Prop) (v : ProbabilityVector ι) (run : FullRun F) : ι :=
  (uncons F (Fintype.card ι) Finset.univ (fullSet_nonempty v) run).1.val

theorem fullRoot_head (F : ι → ι → Prop) (v : ProbabilityVector ι) (run : FullRun F) :
    (pivotList F (Fintype.card ι+1) Finset.univ run).head?=some (fullRoot F v run) := by
  simp only [pivotList,dite_eq_left (fullSet_nonempty v),List.head?_cons,fullRoot]

theorem fullRoot_selected (F : ι → ι → Prop) (v : ProbabilityVector ι) (run : FullRun F) :
    fullRoot F v run∈pivotList F (Fintype.card ι+1) Finset.univ run := by
  simp only [pivotList,dite_eq_left (fullSet_nonempty v),fullRoot,List.mem_cons]
  exact Or.inl True.intro

theorem fullRoot_mean (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (f : ι → ℝ) :
    (fullLaw F v hv).mean (fun run ↦ f (fullRoot F v run))=v.mean f := by
  unfold fullLaw fullRoot
  rw [law_uncons_mean F v hv (Fintype.card ι) Finset.univ (fullSet_nonempty v) (fun chosen ↦ f chosen.1.val)]
  have hfun : (fun s : {i // i∈(Finset.univ:Finset ι)} ↦
      (law F v hv (Fintype.card ι) (survivors F Finset.univ s.val)).mean (fun _ ↦ f s.val))=
        (fun s ↦ f s.val) := by
    funext s
    exact ProbabilityVector.mean_const _ _
  rw [hfun,pivotLaw_mean v hv Finset.univ (fullSet_nonempty v) f,mass_univ,div_one]
  rfl

def randomizedMatrix (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (s i r : ι) : ℝ :=
  (fullLaw F v hv).mean (fun run ↦ ownedIndicator F (Fintype.card ι+1) Finset.univ run s i*
    ((if i=r then 1 else 0)-(if fullRoot F v run=r then 1 else 0)))

theorem ownedIndicator_sum (F : ι → ι → Prop) (run : FullRun F) (i : ι) :
    (∑ s, ownedIndicator F (Fintype.card ι+1) Finset.univ run s i)=1 := by
  obtain ⟨s,hs⟩ := owner_covers F (Fintype.card ι+1) Finset.univ (by simp) run i (Finset.mem_univ i)
  simp [ownedIndicator,hs]

theorem randomizedMatrix_row_sum (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (s i : ι) :
    (∑ r, randomizedMatrix F v hv s i r)=0 := by
  unfold randomizedMatrix
  rw [← ProbabilityVector.mean_sum]
  have hfun : (fun run : FullRun F ↦ ∑ r, ownedIndicator F (Fintype.card ι+1) Finset.univ run s i*
      ((if i=r then 1 else 0)-(if fullRoot F v run=r then 1 else 0)))=(fun _ ↦ 0) := by
    funext run
    rw [← Finset.mul_sum,Finset.sum_sub_distrib]
    simp
  rw [hfun,ProbabilityVector.mean_const]

theorem randomizedMatrix_offdiag (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (s i r : ι) (hir : i≠r) : randomizedMatrix F v hv s i r≤0 := by
  calc
    _ ≤ (fullLaw F v hv).mean (fun _ ↦ 0) := by
      apply ProbabilityVector.mean_mono
      intro run
      by_cases ho : owner F (Fintype.card ι+1) Finset.univ run i=some s
      <;> by_cases hr : fullRoot F v run=r
      <;> simp [ownedIndicator,ho,hr,hir]
    _ = _ := ProbabilityVector.mean_const _ _

theorem randomizedMatrix_support (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (s i r : ι)
    (hsupport : ¬(InClosedNeighborhood F s i ∧ InClosedNeighborhood F s r)) :
    randomizedMatrix F v hv s i r=0 := by
  unfold randomizedMatrix
  have hfun : (fun run : FullRun F ↦ ownedIndicator F (Fintype.card ι+1) Finset.univ run s i*
      ((if i=r then 1 else 0)-(if fullRoot F v run=r then 1 else 0)))=(fun _ ↦ 0) := by
    funext run
    by_cases ho : owner F (Fintype.card ι+1) Finset.univ run i=some s
    · have hi := owner_compares_target F (Fintype.card ι+1) Finset.univ run i s ho
      have hr := owner_compares_root F hF (Fintype.card ι+1) Finset.univ run i s (fullRoot F v run) ho
        (fullRoot_head F v run)
      have hir : i≠r := fun heq ↦ hsupport ⟨hi,heq ▸ hi⟩
      have hrr : fullRoot F v run≠r := fun heq ↦ hsupport ⟨hi,heq ▸ hr⟩
      simp [ownedIndicator,ho,hir,hrr]
    · simp [ownedIndicator,ho]
  rw [hfun,ProbabilityVector.mean_const]

theorem randomizedMatrix_total (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (i r : ι) :
    (∑ s, randomizedMatrix F v hv s i r)=(if i=r then 1 else 0)-v r := by
  unfold randomizedMatrix
  rw [← ProbabilityVector.mean_sum]
  have hfun : (fun run : FullRun F ↦ ∑ s, ownedIndicator F (Fintype.card ι+1) Finset.univ run s i*
      ((if i=r then 1 else 0)-(if fullRoot F v run=r then 1 else 0)))=
        (fun run ↦ (if i=r then 1 else 0)-(if fullRoot F v run=r then 1 else 0)) := by
    funext run
    rw [← Finset.sum_mul,ownedIndicator_sum,one_mul]
  rw [hfun,ProbabilityVector.mean_sub,ProbabilityVector.mean_const,
    fullRoot_mean F v hv (fun j ↦ if j=r then 1 else 0)]
  simp [ProbabilityVector.mean]

theorem randomizedMatrix_diagonal_le_owned (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (s i : ι) :
    randomizedMatrix F v hv s i i≤ownedProb F v hv (Fintype.card ι+1) Finset.univ s i := by
  apply ProbabilityVector.mean_mono
  intro run
  by_cases ho : owner F (Fintype.card ι+1) Finset.univ run i=some s
  <;> by_cases hr : fullRoot F v run=i
  <;> simp [ownedIndicator,ho,hr]

theorem anchor_le_selectedProb (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (s : ι) :
    v s≤selectedProb F v hv (Fintype.card ι+1) Finset.univ s := by
  have heq : (fullLaw F v hv).mean (fun run ↦ if fullRoot F v run=s then 1 else 0)=v s := by
    rw [fullRoot_mean F v hv (fun j ↦ if j=s then 1 else 0)]
    simp [ProbabilityVector.mean]
  rw [← heq]
  apply ProbabilityVector.mean_mono
  intro run
  by_cases hr : fullRoot F v run=s
  · have hmem := fullRoot_selected F v run
    rw [hr] at hmem
    simp [selectedIndicator,hr,hmem]
  · simp only [ite_eq_right hr]
    unfold selectedIndicator
    split <;> norm_num

def randomizedAssignment (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) : ComparisonAssignment F v where
  anchor_pos := hv
  matrix := randomizedMatrix F v hv
  sourceWeight := selectedProb F v hv (Fintype.card ι+1) Finset.univ
  row_sum := randomizedMatrix_row_sum F v hv
  offdiag_nonpos := randomizedMatrix_offdiag F v hv
  support := randomizedMatrix_support F hF v hv
  total_matrix := randomizedMatrix_total F v hv
  load_le_source s i := le_trans (randomizedMatrix_diagonal_le_owned F v hv s i)
    (ownedProb_le_selectedProb F v hv (Fintype.card ι+1) Finset.univ s i)
  balanced_load s i := le_trans (mul_le_mul_of_nonneg_left
    (randomizedMatrix_diagonal_le_owned F v hv s i) (v.nonneg i))
      (ownedProb_balanced F v hv (Fintype.card ι+1) Finset.univ s i)
  anchor_le_source := anchor_le_selectedProb F v hv
  source_le_one := selectedProb_le_one F v hv (Fintype.card ι+1) Finset.univ

theorem randomizedAssignment_totalWeight (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (randomizedAssignment F hF v hv).totalWeight=expectedCount F v hv (Fintype.card ι+1) Finset.univ :=
  selectedProb_sum F v hv (Fintype.card ι+1) Finset.univ

theorem randomizedAssignment_bound (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (randomizedAssignment F hF v hv).totalWeight≤3*v.anchorLog := by
  rw [randomizedAssignment_totalWeight]
  exact expectedCount_le_log F hF v hv _ _

end
end Tournament.Upper.RootedPivots
