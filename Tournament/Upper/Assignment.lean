module

public import Tournament.Upper.LinearErrorMaps
public import Tournament.Graphs.Feedback
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

structure ComparisonAssignment (F : ι → ι → Prop) (v : ProbabilityVector ι) where
  anchor_pos : ∀ i, 0<v i
  matrix : ι → ι → ι → ℝ
  sourceWeight : ι → ℝ
  row_sum : ∀ s i, ∑ r, matrix s i r=0
  offdiag_nonpos : ∀ s i r, i≠r → matrix s i r≤0
  support : ∀ s i r, ¬(InClosedNeighborhood F s i ∧ InClosedNeighborhood F s r) → matrix s i r=0
  total_matrix : ∀ i r, (∑ s, matrix s i r)=(if i=r then 1 else 0)-v r
  load_le_source : ∀ s i, matrix s i i≤sourceWeight s
  balanced_load : ∀ s i, v i*matrix s i i≤v s*sourceWeight i
  anchor_le_source : ∀ s, v s≤sourceWeight s
  source_le_one : ∀ s, sourceWeight s≤1

namespace ComparisonAssignment

variable {F : ι → ι → Prop} {v : ProbabilityVector ι}

def totalWeight (A : ComparisonAssignment F v) : ℝ := ∑ s, A.sourceWeight s

theorem sourceWeight_pos (A : ComparisonAssignment F v) (s : ι) : 0<A.sourceWeight s :=
  lt_of_lt_of_le (A.anchor_pos s) (A.anchor_le_source s)

theorem totalWeight_ge_one (A : ComparisonAssignment F v) : 1≤A.totalWeight := by
  rw [← v.sum_eq_one]
  exact Finset.sum_le_sum (fun s _ ↦ A.anchor_le_source s)

theorem totalWeight_pos (A : ComparisonAssignment F v) : 0<A.totalWeight :=
  lt_of_lt_of_le (by norm_num) A.totalWeight_ge_one

def sourceLaw (A : ComparisonAssignment F v) : ProbabilityVector ι where
  weight s := A.sourceWeight s/A.totalWeight
  nonneg s := div_nonneg (le_of_lt (A.sourceWeight_pos s)) (le_of_lt A.totalWeight_pos)
  sum_eq_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt A.totalWeight_pos)

theorem sourceLaw_pos (A : ComparisonAssignment F v) (s : ι) : 0<A.sourceLaw s :=
  div_pos (A.sourceWeight_pos s) A.totalWeight_pos

theorem totalWeight_mul_sourceLaw (A : ComparisonAssignment F v) (s : ι) :
    A.totalWeight*A.sourceLaw s=A.sourceWeight s := by
  change A.totalWeight*(A.sourceWeight s/A.totalWeight)=A.sourceWeight s
  field_simp [ne_of_gt A.totalWeight_pos]

def act (A : ComparisonAssignment F v) (s : ι) (f : ι → ℝ) : ι → ℝ := applyEstimator A.matrix s f

def edgeWeight (A : ComparisonAssignment F v) (s i r : ι) : ℝ := if i=r then 0 else -A.matrix s i r

theorem edgeWeight_nonneg (A : ComparisonAssignment F v) (s i r : ι) : 0≤A.edgeWeight s i r := by
  unfold edgeWeight
  split
  · exact le_refl _
  · exact neg_nonneg.mpr (A.offdiag_nonpos s i r ‹i≠r›)

theorem edgeWeight_sum (A : ComparisonAssignment F v) (s i : ι) :
    (∑ r, A.edgeWeight s i r)=A.matrix s i i := by
  have hfun : (fun r ↦ A.edgeWeight s i r)=(fun r ↦ (if i=r then A.matrix s i i else 0)-A.matrix s i r) := by
    funext r
    unfold edgeWeight
    split <;> simp_all
  rw [hfun,Finset.sum_sub_distrib,A.row_sum,sub_zero]
  simp

theorem diagonal_nonneg (A : ComparisonAssignment F v) (s i : ι) : 0≤A.matrix s i i := by
  rw [← A.edgeWeight_sum]
  exact Finset.sum_nonneg (fun r _ ↦ A.edgeWeight_nonneg s i r)

theorem edgeWeight_source_sum (A : ComparisonAssignment F v) (i r : ι) :
    (∑ s, A.edgeWeight s i r)=if i=r then 0 else v r := by
  by_cases hir : i=r
  · simp only [edgeWeight,ite_eq_left hir,Finset.sum_const_zero]
  · simp only [edgeWeight,ite_eq_right hir,Finset.sum_neg_distrib,A.total_matrix,zero_sub,neg_neg]

theorem comparison_form (A : ComparisonAssignment F v) (s : ι) (f : ι → ℝ) (i : ι) :
    A.act s f i=∑ r, A.edgeWeight s i r*(f i-f r) := by
  have hterm : ∀ r, A.edgeWeight s i r*(f i-f r)=A.matrix s i r*f r-A.matrix s i r*f i := by
    intro r
    unfold edgeWeight
    split
    · subst r
      ring
    · ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,A.row_sum,zero_mul,sub_zero]
  rfl

theorem act_sq_le (A : ComparisonAssignment F v) (s : ι) (f : ι → ℝ) (i : ι) :
    (A.act s f i)^2≤A.matrix s i i*(∑ r, A.edgeWeight s i r*(f i-f r)^2) := by
  rw [A.comparison_form,← A.edgeWeight_sum]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun r _ ↦ A.edgeWeight_nonneg s i r)
    (fun r _ ↦ mul_nonneg (A.edgeWeight_nonneg s i r) (sq_nonneg (f i-f r)))
    (fun r _ ↦ by nlinarith [sq_nonneg (A.edgeWeight s i r*(f i-f r))])

theorem act_abs_le_diagonal (A : ComparisonAssignment F v) (s : ι) (f : ι → ℝ)
    (hf : BoundedLoss f) (i : ι) : |A.act s f i|≤A.matrix s i i := by
  rw [A.comparison_form,← A.edgeWeight_sum]
  calc
    _ ≤ ∑ r, |A.edgeWeight s i r*(f i-f r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, A.edgeWeight s i r := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul,abs_of_nonneg (A.edgeWeight_nonneg s i r)]
      have hdiff : |f i-f r|≤1 := abs_le.mpr ⟨by have := hf i; have := hf r; linarith,by have := hf i; have := hf r; linarith⟩
      exact mul_le_of_le_one_right (A.edgeWeight_nonneg s i r) hdiff

theorem total_act (A : ComparisonAssignment F v) (f : ι → ℝ) (i : ι) :
    (∑ s, A.act s f i)=v.center f i := by
  unfold act applyEstimator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,A.total_matrix]
  simp [sub_mul,Finset.sum_sub_distrib,ProbabilityVector.center,ProbabilityVector.mean]

end ComparisonAssignment
end
end Tournament.Upper
