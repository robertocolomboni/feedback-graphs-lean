module

public import Tournament.Upper.Assignment

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def midpoint (p q : ProbabilityVector ι) : ProbabilityVector ι where
  weight i := (p i+q i)/2
  nonneg i := by have := p.nonneg i; have := q.nonneg i; positivity
  sum_eq_one := by rw [← Finset.sum_div,Finset.sum_add_distrib,p.sum_eq_one,q.sum_eq_one]; norm_num

theorem squareNorm_divisor (p : ProbabilityVector ι) (f : ι → ℝ) (c : ℝ) :
    p.squareNorm f/c=∑ i, (p i/c)*(f i)^2 := by
  unfold squareNorm
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

theorem pairwise_variance (p : ProbabilityVector ι) (f : ι → ℝ) :
    (∑ i, ∑ r, p i*p r*(f i-f r)^2)=2*p.variance f := by
  have hinner : ∀ i, (∑ r, p i*p r*(f i-f r)^2)=p i*(p.variance f+(f i-p.mean f)^2) := by
    intro i
    calc
      _ = p i*(∑ r, p r*(f r-f i)^2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ ↦ by ring)
      _ = p i*(p.variance f+(p.mean f-f i)^2) := by rw [p.sum_sq_sub_eq_variance_add]
      _ = _ := by ring
  simp_rw [hinner,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,p.sum_eq_one,one_mul]
  change p.variance f+p.variance f=2*p.variance f
  ring

theorem mixed_pairwise_variance_le (p q : ProbabilityVector ι) (f : ι → ℝ) :
    (∑ i, ∑ r, q i*p r*(f i-f r)^2)≤4*(p.midpoint q).variance f := by
  let c := (p.midpoint q).mean f
  have hdiff : ∀ i r, (f i-f r)^2≤2*(f i-c)^2+2*(f r-c)^2 := by
    intro i r
    nlinarith [sq_nonneg ((f i-c)+(f r-c))]
  calc
    _ ≤ ∑ i, ∑ r, q i*p r*(2*(f i-c)^2+2*(f r-c)^2) :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun r _ ↦
        mul_le_mul_of_nonneg_left (hdiff i r) (mul_nonneg (q.nonneg i) (p.nonneg r))))
    _ = 2*(∑ i, q i*(f i-c)^2)+2*(∑ r, p r*(f r-c)^2) := by
      have hinner : ∀ i, (∑ r, q i*p r*(2*(f i-c)^2+2*(f r-c)^2))=
          2*q i*(f i-c)^2+2*q i*(∑ r, p r*(f r-c)^2) := by
        intro i
        calc
          _ = (q i*(2*(f i-c)^2))*(∑ r, p r)+(2*q i)*(∑ r, p r*(f r-c)^2) := by
            rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun r _ ↦ by ring)
          _ = _ := by rw [p.sum_eq_one]; ring
      simp_rw [hinner,Finset.sum_add_distrib]
      have hhead : (∑ i, 2*q i*(f i-c)^2)=2*(∑ i, q i*(f i-c)^2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ by ring)
      have htail : (∑ i, 2*q i*(∑ r, p r*(f r-c)^2))=2*(∑ r, p r*(f r-c)^2) := by
        rw [← Finset.sum_mul]
        have hq : (∑ i, 2*q i)=2 := by rw [← Finset.mul_sum,q.sum_eq_one,mul_one]
        rw [hq]
      rw [hhead,htail]
    _ = _ := by
      unfold variance center midpoint
      change _=4*∑ i, ((p i+q i)/2)*(f i-c)^2
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ by ring)

end
end Tournament.ProbabilityVector

namespace Tournament.Upper.ComparisonAssignment

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop} {v : ProbabilityVector ι}

theorem weighted_edge_sum (A : ComparisonAssignment F v) (u f : ι → ℝ) :
    (∑ s, ∑ i, u i*(∑ r, A.edgeWeight s i r*(f i-f r)^2))=
      ∑ i, ∑ r, u i*v r*(f i-f r)^2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = u i*(∑ s, A.edgeWeight s i r)*(f i-f r)^2 := by
      rw [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ ↦ by ring)
    _ = _ := by
      rw [A.edgeWeight_source_sum]
      split
      · subst r
        ring
      · ring

theorem first_assignment_moment (A : ComparisonAssignment F v) (f : ι → ℝ) :
    (∑ s, v.squareNorm (A.act s f)/A.sourceLaw s)≤2*A.totalWeight*v.variance f := by
  simp_rw [ProbabilityVector.squareNorm_divisor]
  calc
    _ ≤ ∑ s, ∑ i, A.totalWeight*v i*(∑ r, A.edgeWeight s i r*(f i-f r)^2) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro i _
      have hq := A.sourceLaw_pos s
      have hc : (v i/A.sourceLaw s)*A.matrix s i i≤A.totalWeight*v i := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hq).mpr
        have hl := mul_le_mul_of_nonneg_left (A.load_le_source s i) (v.nonneg i)
        rw [← A.totalWeight_mul_sourceLaw s] at hl
        nlinarith
      have hn : 0≤∑ r, A.edgeWeight s i r*(f i-f r)^2 :=
        Finset.sum_nonneg (fun r _ ↦ mul_nonneg (A.edgeWeight_nonneg s i r) (sq_nonneg _))
      calc
        _ ≤ (v i/A.sourceLaw s)*(A.matrix s i i*(∑ r, A.edgeWeight s i r*(f i-f r)^2)) :=
          mul_le_mul_of_nonneg_left (A.act_sq_le s f i) (div_nonneg (v.nonneg i) (le_of_lt hq))
        _ = ((v i/A.sourceLaw s)*A.matrix s i i)*(∑ r, A.edgeWeight s i r*(f i-f r)^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc hn
    _ = A.totalWeight*(∑ s, ∑ i, v i*(∑ r, A.edgeWeight s i r*(f i-f r)^2)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun r _ ↦ by ring)
    _ = _ := by rw [A.weighted_edge_sum,ProbabilityVector.pairwise_variance]; ring

theorem second_assignment_moment (A : ComparisonAssignment F v) (f : ι → ℝ) :
    (∑ s, v.squareNorm (A.act s f)/v s)≤4*A.totalWeight*(v.midpoint A.sourceLaw).variance f := by
  simp_rw [ProbabilityVector.squareNorm_divisor]
  calc
    _ ≤ ∑ s, ∑ i, A.sourceWeight i*(∑ r, A.edgeWeight s i r*(f i-f r)^2) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro i _
      have hv := A.anchor_pos s
      have hc : (v i/v s)*A.matrix s i i≤A.sourceWeight i := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hv).mpr
        nlinarith [A.balanced_load s i]
      have hn : 0≤∑ r, A.edgeWeight s i r*(f i-f r)^2 :=
        Finset.sum_nonneg (fun r _ ↦ mul_nonneg (A.edgeWeight_nonneg s i r) (sq_nonneg _))
      calc
        _ ≤ (v i/v s)*(A.matrix s i i*(∑ r, A.edgeWeight s i r*(f i-f r)^2)) :=
          mul_le_mul_of_nonneg_left (A.act_sq_le s f i) (div_nonneg (v.nonneg i) (le_of_lt hv))
        _ = ((v i/v s)*A.matrix s i i)*(∑ r, A.edgeWeight s i r*(f i-f r)^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc hn
    _ = A.totalWeight*(∑ i, ∑ r, A.sourceLaw i*v r*(f i-f r)^2) := by
      rw [A.weighted_edge_sum]
      simp_rw [← A.totalWeight_mul_sourceLaw]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun r _ ↦ by ring)
    _ ≤ A.totalWeight*(4*(v.midpoint A.sourceLaw).variance f) :=
      mul_le_mul_of_nonneg_left (ProbabilityVector.mixed_pairwise_variance_le v A.sourceLaw f) (le_of_lt A.totalWeight_pos)
    _ = _ := by ring

end
end Tournament.Upper.ComparisonAssignment
