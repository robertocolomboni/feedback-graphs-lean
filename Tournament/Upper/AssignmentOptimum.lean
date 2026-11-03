module

public import Tournament.Upper.PivotAveraging
public import Tournament.Probability.CompactOptimizationSelection
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

namespace ComparisonAssignment

variable {F : ι → ι → Prop} {v : ProbabilityVector ι}

theorem offdiag_lower (A : ComparisonAssignment F v) (s i r : ι) (hir : i≠r) : -v r≤A.matrix s i r := by
  have hle : A.edgeWeight s i r≤∑ t, A.edgeWeight t i r :=
    Finset.single_le_sum (fun t _ ↦ A.edgeWeight_nonneg t i r) (Finset.mem_univ s)
  rw [A.edgeWeight_source_sum,ite_eq_right hir] at hle
  simp only [edgeWeight,ite_eq_right hir] at hle
  linarith

theorem diagonal_upper (A : ComparisonAssignment F v) (s i : ι) : A.matrix s i i≤1-v i := by
  have hle : A.matrix s i i≤∑ t, A.matrix t i i :=
    Finset.single_le_sum (fun t _ ↦ A.diagonal_nonneg t i) (Finset.mem_univ s)
  simpa only [A.total_matrix,ite_true] using hle

theorem entry_bounds (A : ComparisonAssignment F v) (s i r : ι) :
    -1≤A.matrix s i r ∧ A.matrix s i r≤1 := by
  by_cases hir : i=r
  · subst r
    exact ⟨by linarith [A.diagonal_nonneg s i],by linarith [A.diagonal_upper s i,v.nonneg i]⟩
  · exact ⟨by linarith [A.offdiag_lower s i r hir,v.weight_le_one r],
      by linarith [A.offdiag_nonpos s i r hir]⟩

end ComparisonAssignment

abbrev AssignmentData (ι : Type*) := (ι → ι → ι → ℝ) × (ι → ℝ)

def assignmentData {F : ι → ι → Prop} {v : ProbabilityVector ι} (A : ComparisonAssignment F v) : AssignmentData ι :=
  (A.matrix,A.sourceWeight)

def feasibleData (F : ι → ι → Prop) (v : ProbabilityVector ι) : Set (AssignmentData ι) :=
  {d | (∀ s i, ∑ r, d.1 s i r=0) ∧
    (∀ s i r, i≠r → d.1 s i r≤0) ∧
    (∀ s i r, ¬(InClosedNeighborhood F s i ∧ InClosedNeighborhood F s r) → d.1 s i r=0) ∧
    (∀ i r, (∑ s, d.1 s i r)=(if i=r then 1 else 0)-v r) ∧
    (∀ s i, d.1 s i i≤d.2 s) ∧
    (∀ s i, v i*d.1 s i i≤v s*d.2 i) ∧
    (∀ s, v s≤d.2 s) ∧
    (∀ s, d.2 s≤1)}

theorem assignmentData_mem {F : ι → ι → Prop} {v : ProbabilityVector ι} (A : ComparisonAssignment F v) :
    assignmentData A∈feasibleData F v :=
  ⟨A.row_sum,A.offdiag_nonpos,A.support,A.total_matrix,A.load_le_source,A.balanced_load,A.anchor_le_source,A.source_le_one⟩

def assignmentOfData (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (d : AssignmentData ι) (hd : d∈feasibleData F v) : ComparisonAssignment F v where
  anchor_pos := hv
  matrix := d.1
  sourceWeight := d.2
  row_sum := hd.1
  offdiag_nonpos := hd.2.1
  support := hd.2.2.1
  total_matrix := hd.2.2.2.1
  load_le_source := hd.2.2.2.2.1
  balanced_load := hd.2.2.2.2.2.1
  anchor_le_source := hd.2.2.2.2.2.2.1
  source_le_one := hd.2.2.2.2.2.2.2

theorem feasibleData_closed (F : ι → ι → Prop) (v : ProbabilityVector ι) : IsClosed (feasibleData F v) := by
  unfold feasibleData
  simp only [Set.ofPred_and,Set.ofPred_forall]
  repeat' apply IsClosed.inter
  all_goals repeat' (apply isClosed_iInter; intro)
  all_goals first | apply isClosed_eq | apply isClosed_le
  all_goals fun_prop

theorem feasibleData_bounded_box (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    feasibleData F v⊆Set.Icc ((fun _ _ _ ↦ (-1:ℝ)),fun _ ↦ (0:ℝ)) ((fun _ _ _ ↦ (1:ℝ)),fun _ ↦ (1:ℝ)) := by
  intro d hd
  let A := assignmentOfData F v hv d hd
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro s i r
    exact (A.entry_bounds s i r).1
  · intro s
    exact le_trans (v.nonneg s) (A.anchor_le_source s)
  · intro s i r
    exact (A.entry_bounds s i r).2
  · intro s
    exact A.source_le_one s

theorem feasibleData_compact (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    IsCompact (feasibleData F v) :=
  isCompact_Icc.of_isClosed_subset (feasibleData_closed F v) (feasibleData_bounded_box F v hv)

def assignmentObjective (d : AssignmentData ι) : ℝ := ∑ s, d.2 s

theorem assignmentObjective_continuous : Continuous (assignmentObjective (ι := ι)) := by
  unfold assignmentObjective
  fun_prop

abbrev PositiveAssignmentAnchor (ι : Type*) [Fintype ι] :=
  {w : ι → ℝ // (∀ i, 0 < w i) ∧ ∑ i, w i = 1}

def positiveAssignmentAnchor (v : ProbabilityVector ι) (hv : ∀ i, 0 < v i) :
    PositiveAssignmentAnchor ι :=
  ⟨v.weight, hv, v.sum_eq_one⟩

def PositiveAssignmentAnchor.toProbabilityVector (a : PositiveAssignmentAnchor ι) :
    ProbabilityVector ι where
  weight := a.val
  nonneg := fun i ↦ (a.property.1 i).le
  sum_eq_one := a.property.2

theorem toProbabilityVector_positiveAssignmentAnchor (v : ProbabilityVector ι)
    (hv : ∀ i, 0 < v i) :
    (positiveAssignmentAnchor v hv).toProbabilityVector = v := by
  cases v
  rfl

def assignmentBox : Set (AssignmentData ι) :=
  Set.Icc ((fun _ _ _ ↦ (-1 : ℝ)), fun _ ↦ (0 : ℝ))
    ((fun _ _ _ ↦ (1 : ℝ)), fun _ ↦ (1 : ℝ))

omit [Fintype ι] in
theorem assignmentBox_compact : IsCompact (assignmentBox (ι := ι)) := isCompact_Icc

omit [Fintype ι] in
theorem assignmentBox_nonempty : (assignmentBox (ι := ι)).Nonempty := by
  refine ⟨((fun _ _ _ ↦ 0), fun _ ↦ 0), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · intro s i r
    norm_num
  · intro s
    exact le_rfl
  · intro s i r
    norm_num
  · intro s
    norm_num

theorem feasibleData_joint_closed (F : ι → ι → Prop) :
    IsClosed {p : PositiveAssignmentAnchor ι × AssignmentData ι |
      p.2 ∈ feasibleData F p.1.toProbabilityVector} := by
  have hAnchor (i : ι) : Continuous (fun p : PositiveAssignmentAnchor ι × AssignmentData ι ↦ p.1.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  change IsClosed {p : PositiveAssignmentAnchor ι × AssignmentData ι |
    (∀ s i, ∑ r, p.2.1 s i r = 0) ∧
    (∀ s i r, i ≠ r → p.2.1 s i r ≤ 0) ∧
    (∀ s i r, ¬(InClosedNeighborhood F s i ∧ InClosedNeighborhood F s r) → p.2.1 s i r = 0) ∧
    (∀ i r, (∑ s, p.2.1 s i r) = (if i = r then 1 else 0) - p.1.val r) ∧
    (∀ s i, p.2.1 s i i ≤ p.2.2 s) ∧
    (∀ s i, p.1.val i * p.2.1 s i i ≤ p.1.val s * p.2.2 i) ∧
    (∀ s, p.1.val s ≤ p.2.2 s) ∧
    (∀ s, p.2.2 s ≤ 1)}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  repeat' apply IsClosed.inter
  all_goals repeat' (apply isClosed_iInter; intro)
  all_goals first | apply isClosed_eq | apply isClosed_le
  all_goals fun_prop

theorem exists_measurable_optimal_assignmentData (F : ι → ι → Prop) (hF : IsTournament F) :
    ∃ g : PositiveAssignmentAnchor ι → AssignmentData ι, Measurable g ∧
      ∀ a, g a ∈ feasibleData F a.toProbabilityVector ∧
        ∀ d ∈ feasibleData F a.toProbabilityVector,
          assignmentObjective (g a) ≤ assignmentObjective d := by
  obtain ⟨g, hg, hopt⟩ :=
    Tournament.Probability.CompactOptimization.exists_measurable_minimizer_on_compact
      (assignmentBox (ι := ι)) assignmentBox_compact assignmentBox_nonempty
      (fun (a : PositiveAssignmentAnchor ι) d ↦ d ∈ feasibleData F a.toProbabilityVector)
      assignmentObjective (feasibleData_joint_closed F) assignmentObjective_continuous
      (fun a ↦ by
        let A := RootedPivots.randomizedAssignment F hF a.toProbabilityVector a.property.1
        have hA : assignmentData A ∈ feasibleData F a.toProbabilityVector := assignmentData_mem A
        exact ⟨assignmentData A,
          feasibleData_bounded_box F a.toProbabilityVector a.property.1 hA, hA⟩)
  refine ⟨g, hg, ?_⟩
  intro a
  refine ⟨(hopt a).2.1, ?_⟩
  intro d hd
  exact (hopt a).2.2 d (feasibleData_bounded_box F a.toProbabilityVector a.property.1 hd) hd

def optimalAssignmentData (F : ι → ι → Prop) (hF : IsTournament F) :
    PositiveAssignmentAnchor ι → AssignmentData ι :=
  Classical.choose (exists_measurable_optimal_assignmentData F hF)

theorem optimalAssignmentData_measurable (F : ι → ι → Prop) (hF : IsTournament F) :
    Measurable (optimalAssignmentData F hF) :=
  (Classical.choose_spec (exists_measurable_optimal_assignmentData F hF)).1

theorem optimalAssignmentData_mem (F : ι → ι → Prop) (hF : IsTournament F)
    (a : PositiveAssignmentAnchor ι) :
    optimalAssignmentData F hF a ∈ feasibleData F a.toProbabilityVector :=
  ((Classical.choose_spec (exists_measurable_optimal_assignmentData F hF)).2 a).1

theorem optimalAssignmentData_isOptimal (F : ι → ι → Prop) (hF : IsTournament F)
    (a : PositiveAssignmentAnchor ι) (d : AssignmentData ι)
    (hd : d ∈ feasibleData F a.toProbabilityVector) :
    assignmentObjective (optimalAssignmentData F hF a) ≤ assignmentObjective d :=
  ((Classical.choose_spec (exists_measurable_optimal_assignmentData F hF)).2 a).2 d hd

def optimizedAssignment (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) : ComparisonAssignment F v :=
  assignmentOfData F v hv (optimalAssignmentData F hF (positiveAssignmentAnchor v hv)) (by
    simpa only [toProbabilityVector_positiveAssignmentAnchor] using
      optimalAssignmentData_mem F hF (positiveAssignmentAnchor v hv))

theorem optimizedAssignment_isOptimal (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (B : ComparisonAssignment F v) :
    (optimizedAssignment F hF v hv).totalWeight≤B.totalWeight := by
  apply optimalAssignmentData_isOptimal F hF (positiveAssignmentAnchor v hv) (assignmentData B)
  simpa only [toProbabilityVector_positiveAssignmentAnchor] using assignmentData_mem B

theorem optimizedAssignment_spec (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (∀ B : ComparisonAssignment F v, (optimizedAssignment F hF v hv).totalWeight≤B.totalWeight) ∧
      1≤(optimizedAssignment F hF v hv).totalWeight ∧
        (optimizedAssignment F hF v hv).totalWeight≤3*v.anchorLog := by
  refine ⟨optimizedAssignment_isOptimal F hF v hv,
    (optimizedAssignment F hF v hv).totalWeight_ge_one, ?_⟩
  exact (optimizedAssignment_isOptimal F hF v hv (RootedPivots.randomizedAssignment F hF v hv)).trans
    (RootedPivots.randomizedAssignment_bound F hF v hv)

theorem optimizedAssignment_bounds (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    1≤(optimizedAssignment F hF v hv).totalWeight ∧ (optimizedAssignment F hF v hv).totalWeight≤3*v.anchorLog :=
  (optimizedAssignment_spec F hF v hv).2

theorem rooted_assignment_optimum (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    ∃ A : ComparisonAssignment F v, (∀ B : ComparisonAssignment F v, A.totalWeight≤B.totalWeight) ∧
      1≤A.totalWeight ∧ A.totalWeight≤3*v.anchorLog :=
  ⟨optimizedAssignment F hF v hv, optimizedAssignment_spec F hF v hv⟩

end
end Tournament.Upper
