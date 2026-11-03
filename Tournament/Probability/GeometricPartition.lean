module

public import Tournament.Probability.PairQuadratic
public import Tournament.Probability.FiniteKernel

@[expose] public section

namespace Tournament.GeometricPartition

open scoped BigOperators Classical

noncomputable section

def quadratic (χ : ℝ) (y : ℕ → ℝ) (offset h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
    χ^(Nat.dist t u)*y (offset+t)*y (offset+u)

theorem quadratic_eq_diagonal_pairs (χ : ℝ) (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic χ y offset h = (∑ t ∈ Finset.range h, y (offset+t)^2)+
      2*(∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
        if t<u then χ^(u-t)*y (offset+t)*y (offset+u) else 0) := by
  let A : ℕ → ℕ → ℝ := fun t u ↦ χ^(Nat.dist t u)*y (offset+t)*y (offset+u)
  have hsym : ∀ t u, A t u=A u t := by
    intro t u
    dsimp only [A]
    rw [Nat.dist_comm]
    ring
  have hs := Restarts.symmetric_double_sum A hsym h
  have hdiag : (∑ t ∈ Finset.range h, A t t) = ∑ t ∈ Finset.range h, y (offset+t)^2 := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [A,Nat.dist_self,pow_zero,one_mul,pow_two]
  have hpairs : Restarts.orderedPairSum A 0 h =
      ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
        if t<u then χ^(u-t)*y (offset+t)*y (offset+u) else 0 := by
    unfold Restarts.orderedPairSum
    simp only [Nat.zero_add]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    by_cases htu : t<u
    · simp only [ite_eq_left htu,A,Nat.dist_eq_sub_of_le (Nat.le_of_lt htu)]
    · simp only [ite_eq_right htu]
  rw [hdiag,hpairs] at hs
  exact hs

theorem quadratic_eq_mean_chunkSquares {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (y : ℕ → ℝ) (offset n : ℕ) :
    quadratic χ y offset (n+1) =
      (Restarts.law (1-χ) (sub_nonneg.mpr hχ1) (by linarith) n).mean
        (fun coins ↦ Restarts.chunkSquareSum y offset (Restarts.parts n coins)) := by
  have heq : (fun coins : Restarts.Coins n ↦ Restarts.chunkSquareSum y offset (Restarts.parts n coins)) =
      (fun coins ↦ (∑ t ∈ Finset.range (n+1), y (offset+t)^2)+
        2*Restarts.chunkSum (fun start k ↦ Restarts.orderedPairSum (fun t u ↦ y t*y u) start (k+1))
          offset (Restarts.parts n coins)) := by
    funext coins
    rw [Restarts.chunkSquareSum_eq_diagonal_pairs,Restarts.parts_totalRounds]
  rw [heq,ProbabilityVector.mean_add,ProbabilityVector.mean_const,ProbabilityVector.mean_const_mul]
  change quadratic χ y offset (n+1) = (∑ t ∈ Finset.range (n+1), y (offset+t)^2)+
    2*Restarts.chunkSumMean (1-χ) (sub_nonneg.mpr hχ1) (by linarith)
      (fun start k ↦ Restarts.orderedPairSum (fun t u ↦ y t*y u) start (k+1)) n offset
  rw [Restarts.chunkSumMean_orderedPairSum]
  have hval : 1-(1-χ)=χ := by ring
  rw [hval,quadratic_eq_diagonal_pairs]
  congr 2
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  split <;> ring

theorem quadratic_nonneg {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (y : ℕ → ℝ) (offset h : ℕ) : 0 ≤ quadratic χ y offset h := by
  cases h with
  | zero => simp [quadratic]
  | succ n =>
    rw [quadratic_eq_mean_chunkSquares hχ hχ1]
    exact ProbabilityVector.mean_nonneg _ (fun coins ↦ Restarts.chunkSquareSum_nonneg y offset (Restarts.parts n coins))

variable {ι : Type*} [Fintype ι]

def vectorQuadratic (p : ProbabilityVector ι) (χ : ℝ) (g : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
    χ^(Nat.dist t u)*FiniteKernel.weightedInner p (g (offset+t)) (g (offset+u))

def chunkVectorSquareSum (p : ProbabilityVector ι) (g : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  Restarts.chunkSum (fun start n ↦ p.squareNorm (fun i ↦ ∑ t ∈ Finset.range (n+1), g (start+t) i)) offset ns

theorem vectorQuadratic_coordinates (p : ProbabilityVector ι) (χ : ℝ) (g : ℕ → ι → ℝ)
    (offset h : ℕ) :
    vectorQuadratic p χ g offset h = ∑ i, p i*quadratic χ (fun t ↦ g t i) offset h := by
  unfold vectorQuadratic quadratic FiniteKernel.weightedInner ProbabilityVector.mean
  simp only [Finset.mul_sum]
  calc
    _ = ∑ t ∈ Finset.range h, ∑ i, ∑ u ∈ Finset.range h,
        χ^(Nat.dist t u)*(p i*(g (offset+t) i*g (offset+u) i)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = ∑ i, ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
        χ^(Nat.dist t u)*(p i*(g (offset+t) i*g (offset+u) i)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      ring

theorem chunkVectorSquareSum_coordinates (p : ProbabilityVector ι) (g : ℕ → ι → ℝ)
    (offset : ℕ) (ns : List ℕ) :
    chunkVectorSquareSum p g offset ns = ∑ i, p i*Restarts.chunkSquareSum (fun t ↦ g t i) offset ns := by
  induction ns generalizing offset with
  | nil => simp [chunkVectorSquareSum,Restarts.chunkSum,Restarts.chunkSquareSum]
  | cons n ns ih =>
    change p.squareNorm (fun i ↦ ∑ t ∈ Finset.range (n+1), g (offset+t) i)+
      chunkVectorSquareSum p g (offset+(n+1)) ns = _
    rw [ih]
    simp only [Restarts.chunkSquareSum,Restarts.chunkSum,mul_add,Finset.sum_add_distrib]
    rfl

theorem vectorQuadratic_eq_mean_chunkSquares (p : ProbabilityVector ι) {χ : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (g : ℕ → ι → ℝ) (offset n : ℕ) :
    vectorQuadratic p χ g offset (n+1) =
      (Restarts.law (1-χ) (sub_nonneg.mpr hχ1) (by linarith) n).mean
        (fun coins ↦ chunkVectorSquareSum p g offset (Restarts.parts n coins)) := by
  have heq : (fun coins : Restarts.Coins n ↦ chunkVectorSquareSum p g offset (Restarts.parts n coins)) =
      (fun coins ↦ ∑ i, p i*Restarts.chunkSquareSum (fun t ↦ g t i) offset (Restarts.parts n coins)) := by
    funext coins
    exact chunkVectorSquareSum_coordinates p g offset (Restarts.parts n coins)
  rw [heq,ProbabilityVector.mean_sum,vectorQuadratic_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityVector.mean_const_mul,quadratic_eq_mean_chunkSquares hχ hχ1]

end
end Tournament.GeometricPartition
