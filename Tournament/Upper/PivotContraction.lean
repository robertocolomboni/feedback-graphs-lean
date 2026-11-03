module

public import Tournament.Upper.RootedPivots
public import Tournament.Upper.Scores

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem survivor_mass_sum (F : ι → ι → Prop) (hF : IsTournament F) (v : ProbabilityVector ι)
    (U : Finset ι) (s : ι) :
    mass v (survivors F U s)=∑ j : {i // i∈U}, if j.val≠s ∧ F j.val s then v j.val else 0 := by
  rw [Finset.sum_coe_sort U (fun j ↦ if j≠s ∧ F j s then v j else 0)]
  unfold mass survivors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (¬InClosedNeighborhood F s j)↔j≠s ∧ F j s := by
    have hmem := survivor_iff F hF U s j
    simpa only [survivors,Finset.mem_filter,hj,true_and] using hmem
  simp only [heq]

theorem weighted_pivot_pair_count (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (U : Finset ι) :
    2*(∑ s ∈ U, v s*mass v (survivors F U s))=(mass v U)^2-∑ i ∈ U, (v i)^2 := by
  let a : {i // i∈U} → {i // i∈U} → ℝ := fun i j ↦ if i=j then 0 else v i.val*v j.val
  have hrestrict : IsTournament (fun i j : {i // i∈U} ↦ F i.val j.val) := by
    intro i j hij
    exact hF i.val j.val (fun heq ↦ hij (Subtype.ext heq))
  have hsym : ∀ i j, a i j=a j i := by
    intro i j
    by_cases hij : i=j
    · subst j; rfl
    · simp only [a,ite_eq_right hij,ite_eq_right (Ne.symm hij),mul_comm]
  have hdiag : ∀ i, a i i=0 := fun i ↦ ite_eq_left rfl
  have hcount := tournament_oriented_sum _ hrestrict a hsym hdiag
  have hfull : (∑ i, ∑ j, a i j)=(∑ i : {j // j∈U}, v i.val)^2-∑ i : {j // j∈U}, (v i.val)^2 := by
    have heq : ∀ i j, a i j=v i.val*v j.val-(if i=j then (v i.val)^2 else 0) := by
      intro i j
      by_cases hij : i=j
      · subst j; simp [a,pow_two]
      · simp only [a,ite_eq_right hij,sub_zero]
    simp_rw [heq,Finset.sum_sub_distrib]
    have hsq : (∑ i : {j // j∈U}, v i.val)^2=∑ i : {j // j∈U}, ∑ j : {j // j∈U}, v i.val*v j.val := by
      rw [pow_two,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ ↦ Finset.mul_sum _ _ _)
    rw [hsq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hnum : (∑ s : {i // i∈U}, v s.val*mass v (survivors F U s.val))=
      ∑ i, ∑ j, if F i.val j.val then a i j else 0 := by
    simp_rw [survivor_mass_sum F hF,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i=j
    · subst j
      simp only [ne_eq,not_true_eq_false,false_and,ite_false,mul_zero,a,ite_eq_left rfl,ite_self]
    · have hval : i.val≠j.val := fun heq ↦ hij (Subtype.ext heq)
      by_cases he : F i.val j.val
      · simp only [hval,ne_eq,not_false_eq_true,he,true_and,ite_true,a,ite_eq_right hij]
        ring
      · simp only [he,and_false,ite_false,mul_zero]
  rw [← hnum,hfull] at hcount
  rw [Finset.sum_coe_sort U (fun s ↦ v s*mass v (survivors F U s)),
    Finset.sum_coe_sort U (fun i ↦ v i),Finset.sum_coe_sort U (fun i ↦ (v i)^2)] at hcount
  exact hcount.symm

theorem pivot_remaining_mass_identity (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) (hU : U.Nonempty) :
    (pivotLaw v hv U hU).mean (fun s ↦ mass v (survivors F U s.val))=
      ((mass v U)^2-∑ i ∈ U, (v i)^2)/(2*mass v U) := by
  rw [pivotLaw_mean v hv U hU (fun s ↦ mass v (survivors F U s))]
  have hpair := weighted_pivot_pair_count F hF v U
  have hpos := mass_pos v hv U hU
  field_simp [ne_of_gt hpos]
  nlinarith

theorem pivot_remaining_mass_le_half (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (U : Finset ι) (hU : U.Nonempty) :
    (pivotLaw v hv U hU).mean (fun s ↦ mass v (survivors F U s.val))≤mass v U/2 := by
  rw [pivot_remaining_mass_identity F hF]
  apply (div_le_iff₀ (show 0<2*mass v U by have := mass_pos v hv U hU; positivity)).mpr
  have hdiag : 0≤∑ i ∈ U, (v i)^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  nlinarith

end
end Tournament.Upper.RootedPivots
