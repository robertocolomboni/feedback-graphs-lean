module

public import Tournament.Upper.PivotProcessMoments
public import Tournament.Probability.PartitionRowBound

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def expectedCount (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) : ℝ :=
  (law F v hv n U).mean (fun run ↦ ((pivotList F n U run).length:ℝ))

def survival (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) : ℝ :=
  (law F v hv n U).mean (fun run ↦ if (remainder F n U run).Nonempty then 1 else 0)

theorem survival_probability (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    survival F v hv n U=(law F v hv n U).probability (fun run ↦ (remainder F n U run).Nonempty) := by
  unfold survival ProbabilityVector.probability
  congr 1
  funext run
  by_cases h : (remainder F n U run).Nonempty
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem survival_le_one (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    survival F v hv n U≤1 := by
  calc
    _ ≤ (law F v hv n U).mean (fun _ ↦ 1) := by
      apply ProbabilityVector.mean_mono
      intro run
      split <;> norm_num
    _ = 1 := ProbabilityVector.mean_const _ _

theorem survival_geometric_le (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    survival F v hv n U≤(1/2:ℝ)^n/v.minimumWeight := by
  rw [survival_probability]
  exact surviving_probability_le F hF v hv n U

theorem survival_succ (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty) :
    survival F v hv (n+1) U=(pivotLaw v hv U hU).mean (fun s ↦ survival F v hv n (survivors F U s.val)) :=
  remainder_mean_succ F v hv n U hU (fun V ↦ if V.Nonempty then 1 else 0)

theorem survival_empty (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) :
    survival F v hv n ∅=0 := by
  unfold survival
  rw [remainder_mean_empty F v hv n (fun V ↦ if V.Nonempty then 1 else 0)]
  simp

theorem survival_zero (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) :
    survival F v hv 0 U=if U.Nonempty then 1 else 0 := by
  change (law F v hv 0 U).mean (fun _ ↦ if U.Nonempty then 1 else 0)=_
  exact ProbabilityVector.mean_const _ _

theorem expectedCount_zero (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) :
    expectedCount F v hv 0 U=0 := by
  unfold expectedCount
  simp only [pivotList, List.length_nil, Nat.cast_zero]
  exact ProbabilityVector.mean_const _ _

theorem expectedCount_empty (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) :
    expectedCount F v hv n ∅=0 := by
  have hfun : (fun run : Run F n ∅ ↦ ((pivotList F n ∅ run).length:ℝ))=(fun _ ↦ 0) := by
    funext run
    cases n with
    | zero => simp [pivotList]
    | succ n => simp [pivotList]
  unfold expectedCount
  rw [hfun,ProbabilityVector.mean_const]

theorem expectedCount_succ (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty) :
    expectedCount F v hv (n+1) U=1+(pivotLaw v hv U hU).mean
      (fun s ↦ expectedCount F v hv n (survivors F U s.val)) := by
  have hfun : (fun run : Run F (n+1) U ↦ ((pivotList F (n+1) U run).length:ℝ))=
      (fun run ↦ 1+((pivotList F n (survivors F U (uncons F n U hU run).1.val) (uncons F n U hU run).2).length:ℝ)) := by
    funext run
    rw [pivotList,dite_eq_left hU]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring
  unfold expectedCount
  rw [hfun,ProbabilityVector.mean_add,ProbabilityVector.mean_const]
  congr 1
  exact law_uncons_mean F v hv n U hU (fun chosen ↦
    ((pivotList F n (survivors F U chosen.1.val) chosen.2).length:ℝ))

theorem expectedCount_eq_survival_sum (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) : expectedCount F v hv n U=∑ k ∈ Finset.range n, survival F v hv k U := by
  induction n generalizing U with
  | zero => rw [expectedCount_zero]; simp
  | succ n ih =>
    by_cases hU : U.Nonempty
    · rw [expectedCount_succ F v hv n U hU]
      simp_rw [ih]
      rw [ProbabilityVector.mean_sum]
      have htail : (∑ k ∈ Finset.range n, (pivotLaw v hv U hU).mean
          (fun s ↦ survival F v hv k (survivors F U s.val)))=
            ∑ k ∈ Finset.range n, survival F v hv (k+1) U := by
        exact Finset.sum_congr rfl (fun k _ ↦ (survival_succ F v hv k U hU).symm)
      rw [htail,Finset.sum_range_succ',survival_zero,ite_eq_left hU]
      ring
    · have hU0 : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      rw [expectedCount_empty]
      simp_rw [survival_empty]
      simp

theorem expectedCount_le_threshold (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n B : ℕ) (hB : (1/2:ℝ)^B≤v.minimumWeight) (U : Finset ι) :
    expectedCount F v hv n U≤(B:ℝ)+2 := by
  rw [expectedCount_eq_survival_sum]
  have hprefix (b : ℕ) : (∑ k ∈ Finset.range b, survival F v hv k U)≤(b:ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range b, (1:ℝ) := Finset.sum_le_sum (fun k _ ↦ survival_le_one F v hv k U)
      _ = _ := by simp
  by_cases hn : n≤B
  · have hcast : (n:ℝ)≤(B:ℝ) := by exact_mod_cast hn
    exact le_trans (hprefix n) (by linarith)
  · have hmin := v.minimumWeight_pos hv
    have htail : (∑ j ∈ Finset.range (n-B), survival F v hv (B+j) U)≤2 := by
      calc
        _ ≤ ∑ j ∈ Finset.range (n-B), (1/2:ℝ)^j := by
          apply Finset.sum_le_sum
          intro j _
          have hs := survival_geometric_le F hF v hv (B+j) U
          have hdiv : (1/2:ℝ)^(B+j)/v.minimumWeight≤(1/2:ℝ)^j := by
            apply (div_le_iff₀ hmin).mpr
            rw [pow_add]
            have hm := mul_le_mul_of_nonneg_right hB (show 0≤(1/2:ℝ)^j by positivity)
            nlinarith
          exact le_trans hs hdiv
        _ ≤ _ := by
          have hg := GeometricPartition.geometric_sum_le (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) (n-B)
          norm_num at hg
          exact hg
    rw [show n=B+(n-B) by omega,Finset.sum_range_add]
    exact add_le_add (hprefix B) htail

end
end Tournament.Upper.RootedPivots
