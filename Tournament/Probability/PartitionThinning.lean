module

public import Tournament.Probability.ChunkTotals
public import Tournament.Probability.ThinnedRestarts
public import Tournament.Probability.PartitionLower

@[expose] public section

namespace Tournament.GeometricPartition

open scoped BigOperators Classical

noncomputable section

theorem compressedQuadratic_mean {τ q : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hprod : τ*q ≤ 1) (y : ℕ → ℝ) (offset n : ℕ) :
    (Restarts.law τ hτ hτ1 n).mean
      (fun cuts ↦ compressedQuadratic (1-q) y offset (Restarts.parts n cuts)) =
        quadratic (1-τ*q) y offset (n+1) := by
  have heq : (fun cuts : Restarts.Coins n ↦ compressedQuadratic (1-q) y offset (Restarts.parts n cuts)) =
      (fun cuts ↦ ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        (1-q)^(Nat.dist (Restarts.chunkIndex (Restarts.parts n cuts) t) (Restarts.chunkIndex (Restarts.parts n cuts) u))*
          y (offset+t)*y (offset+u)) := by
    funext cuts
    rw [compressedQuadratic_pullback,Restarts.parts_totalRounds]
  rw [heq]
  unfold quadratic
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [ProbabilityVector.mean_mul_const,ProbabilityVector.mean_mul_const,
    Restarts.intervalDistance_generating hτ hτ1 hq hq1 hprod n t u
      (by have := Finset.mem_range.mp ht; omega) (by have := Finset.mem_range.mp hu; omega)]

theorem quadratic_comparison {χ χ' : ℝ} (hχ' : 0 ≤ χ') (hχ'χ : χ' ≤ χ) (hχ1 : χ < 1)
    (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic χ y offset h ≤ (2*(1-χ')/(1-χ))*quadratic χ' y offset h := by
  have hχ'1 : χ' < 1 := lt_of_le_of_lt hχ'χ hχ1
  have hden : 0 < 1-χ' := sub_pos.mpr hχ'1
  let r : ℝ := (χ-χ')/(1-χ')
  let τ : ℝ := 1-χ'
  let q : ℝ := 1-r
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hχ'χ) (le_of_lt hden)
  have hr1 : r < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hτ : 0 ≤ τ := le_of_lt hden
  have hτ1 : τ ≤ 1 := by dsimp only [τ]; linarith
  have hq : 0 ≤ q := le_of_lt (sub_pos.mpr hr1)
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith
  have hprod : τ*q ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hτ1 hq
    nlinarith
  have hretain : (1-χ')*(1-r)=1-χ := by
    dsimp only [r]
    field_simp [ne_of_gt hden]
    ring
  have hcoarse : 1-τ*q=χ := by
    dsimp only [τ,q]
    linarith
  have hrq : 1-q=r := by dsimp only [q]; ring
  have hfactor : 2/(1-r)=2*(1-χ')/(1-χ) := by
    apply (div_eq_div_iff (ne_of_gt (sub_pos.mpr hr1)) (ne_of_gt (sub_pos.mpr hχ1))).mpr
    nlinarith
  cases h with
  | zero => simp [quadratic]
  | succ n =>
    calc
      quadratic χ y offset (n+1) = (Restarts.law τ hτ hτ1 n).mean
          (fun cuts ↦ compressedQuadratic r y offset (Restarts.parts n cuts)) := by
        have hm := compressedQuadratic_mean hτ hτ1 hq hq1 hprod y offset n
        rw [hrq,hcoarse] at hm
        exact hm.symm
      _ ≤ (Restarts.law τ hτ hτ1 n).mean
          (fun cuts ↦ (2/(1-r))*Restarts.chunkSquareSum y offset (Restarts.parts n cuts)) := by
        exact ProbabilityVector.mean_mono _ (fun cuts ↦ compressedQuadratic_le_chunkSquares hr hr1 y offset (Restarts.parts n cuts))
      _ = (2/(1-r))*quadratic χ' y offset (n+1) := by
        rw [ProbabilityVector.mean_const_mul]
        congr 1
        exact (quadratic_eq_mean_chunkSquares hχ' (le_of_lt hχ'1) y offset n).symm
      _ = _ := by rw [hfactor]

variable {ι : Type*} [Fintype ι]

theorem vectorQuadratic_comparison (p : ProbabilityVector ι) {χ χ' : ℝ}
    (hχ' : 0 ≤ χ') (hχ'χ : χ' ≤ χ) (hχ1 : χ < 1)
    (g : ℕ → ι → ℝ) (offset h : ℕ) :
    vectorQuadratic p χ g offset h ≤ (2*(1-χ')/(1-χ))*vectorQuadratic p χ' g offset h := by
  rw [vectorQuadratic_coordinates,vectorQuadratic_coordinates,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := mul_le_mul_of_nonneg_left (quadratic_comparison hχ' hχ'χ hχ1 (fun t ↦ g t i) offset h) (p.nonneg i)
  simpa only [mul_left_comm] using hi

omit [Fintype ι] in

theorem geometric_partition {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1)
    (y : ℕ → ℝ) (offset n : ℕ) :
    (quadratic χ y offset (n+1) =
      (Restarts.law (1-χ) (sub_nonneg.mpr (le_of_lt hχ1)) (by linarith) n).mean
        (fun cuts ↦ Restarts.chunkSquareSum y offset (Restarts.parts n cuts))) ∧
    (0 ≤ quadratic χ y offset (n+1)) ∧
    (∀ χ', 0 ≤ χ' → χ' ≤ χ →
      quadratic χ y offset (n+1) ≤ (2*(1-χ')/(1-χ))*quadratic χ' y offset (n+1)) ∧
    ((∑ t ∈ Finset.range (n+1), y (offset+t))^2/(1+(1-χ)*(n:ℝ)) ≤ quadratic χ y offset (n+1)) := by
  refine ⟨quadratic_eq_mean_chunkSquares hχ (le_of_lt hχ1) y offset n,
    quadratic_nonneg hχ (le_of_lt hχ1) y offset (n+1),?_,
    constant_vector_lower hχ (le_of_lt hχ1) y offset n⟩
  intro χ' hχ' hχ'χ
  exact quadratic_comparison hχ' hχ'χ hχ1 y offset (n+1)

end
end Tournament.GeometricPartition
