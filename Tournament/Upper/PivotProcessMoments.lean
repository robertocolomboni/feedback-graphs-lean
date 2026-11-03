module

public import Tournament.Upper.PivotContraction

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem remainder_mean_succ (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (U : Finset ι) (hU : U.Nonempty) (g : Finset ι → ℝ) :
    (law F v hv (n+1) U).mean (fun run ↦ g (remainder F (n+1) U run))=
      (pivotLaw v hv U hU).mean (fun s ↦
        (law F v hv n (survivors F U s.val)).mean (fun rest ↦ g (remainder F n (survivors F U s.val) rest))) := by
  rw [law]
  rw [dite_eq_left hU,ProbabilityVector.reindex_mean]
  have hfun : (fun chosen : (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) ↦
      g (remainder F (n+1) U ((uncons F n U hU).symm chosen)))=
        (fun chosen ↦ g (remainder F n (survivors F U chosen.1.val) chosen.2)) := by
    funext chosen
    rw [remainder,dite_eq_left hU]
    exact congrArg (fun pair : (Σ s : {i // i∈U}, Run F n (survivors F U s.val)) ↦
      g (remainder F n (survivors F U pair.1.val) pair.2)) ((uncons F n U hU).apply_symm_apply chosen)
  change ((pivotLaw v hv U hU).sigmaJoint (fun s ↦ law F v hv n (survivors F U s.val))).mean
    (fun chosen ↦ g (remainder F (n+1) U ((uncons F n U hU).symm chosen)))=_
  rw [hfun]
  exact ProbabilityVector.sigmaJoint_mean (pivotLaw v hv U hU)
    (fun s ↦ law F v hv n (survivors F U s.val)) _

omit [Fintype ι] in
theorem remainder_empty (F : ι → ι → Prop) (n : ℕ) (run : Run F n ∅) : remainder F n ∅ run=∅ :=
  remainder_empty_of_card_le F n ∅ (by simp) run

theorem remainder_mean_empty (F : ι → ι → Prop) (v : ProbabilityVector ι) (hv : ∀ i, 0<v i)
    (n : ℕ) (g : Finset ι → ℝ) :
    (law F v hv n ∅).mean (fun run ↦ g (remainder F n ∅ run))=g ∅ := by
  have hfun : (fun run : Run F n ∅ ↦ g (remainder F n ∅ run))=(fun _ ↦ g ∅) := by
    funext run
    rw [remainder_empty]
  rw [hfun,ProbabilityVector.mean_const]

theorem expected_remaining_mass_le (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    (law F v hv n U).mean (fun run ↦ mass v (remainder F n U run))≤(1/2:ℝ)^n*mass v U := by
  induction n generalizing U with
  | zero =>
    change (law F v hv 0 U).mean (fun _ ↦ mass v U)≤_
    rw [ProbabilityVector.mean_const,pow_zero,one_mul]
  | succ n ih =>
    by_cases hU : U.Nonempty
    · rw [remainder_mean_succ F v hv n U hU]
      calc
        _ ≤ (pivotLaw v hv U hU).mean (fun s ↦ (1/2:ℝ)^n*mass v (survivors F U s.val)) :=
          ProbabilityVector.mean_mono _ (fun s ↦ ih (survivors F U s.val))
        _ = (1/2:ℝ)^n*(pivotLaw v hv U hU).mean (fun s ↦ mass v (survivors F U s.val)) :=
          ProbabilityVector.mean_const_mul _ _ _
        _ ≤ (1/2:ℝ)^n*(mass v U/2) := mul_le_mul_of_nonneg_left
          (pivot_remaining_mass_le_half F hF v hv U hU) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    · have hU0 : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      rw [remainder_mean_empty,mass_empty,mul_zero]

theorem minimumWeight_le_nonempty_mass (v : ProbabilityVector ι) (U : Finset ι) (hU : U.Nonempty) :
    v.minimumWeight≤mass v U := by
  obtain ⟨i,hi⟩ := hU
  exact le_trans (v.minimumWeight_le i) (Finset.single_le_sum (fun j _ ↦ v.nonneg j) hi)

theorem surviving_probability_le (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    (law F v hv n U).probability (fun run ↦ (remainder F n U run).Nonempty)≤
      (1/2:ℝ)^n/v.minimumWeight := by
  have hind : (law F v hv n U).probability (fun run ↦ (remainder F n U run).Nonempty)=
      (law F v hv n U).mean (fun run ↦ if (remainder F n U run).Nonempty then 1 else 0) := by
    unfold ProbabilityVector.probability
    congr 1
    funext run
    by_cases h : (remainder F n U run).Nonempty
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h]
  rw [hind]
  have hmin := v.minimumWeight_pos hv
  have hpoint : ∀ run : Run F n U,
      v.minimumWeight*(if (remainder F n U run).Nonempty then 1 else 0)≤mass v (remainder F n U run) := by
    intro run
    split
    · rw [mul_one]
      exact minimumWeight_le_nonempty_mass v _ ‹_›
    · rw [mul_zero]
      exact mass_nonneg v _
  have hm := (law F v hv n U).mean_mono hpoint
  rw [ProbabilityVector.mean_const_mul] at hm
  apply (le_div_iff₀ hmin).mpr
  calc
    _ = v.minimumWeight*(law F v hv n U).mean (fun run ↦ if (remainder F n U run).Nonempty then 1 else 0) := mul_comm _ _
    _ ≤ (law F v hv n U).mean (fun run ↦ mass v (remainder F n U run)) := hm
    _ ≤ (1/2:ℝ)^n*mass v U := expected_remaining_mass_le F hF v hv n U
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (mass_le_one v U)

end
end Tournament.Upper.RootedPivots
