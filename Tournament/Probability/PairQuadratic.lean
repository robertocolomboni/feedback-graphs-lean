module

public import Tournament.Probability.ChunkPairs
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace Tournament.Restarts

open scoped BigOperators Classical

noncomputable section

theorem orderedPairSum_succ (A : ℕ → ℕ → ℝ) (offset h : ℕ) :
    orderedPairSum A offset (h+1) = orderedPairSum A offset h+
      ∑ t ∈ Finset.range h, A (offset+t) (offset+h) := by
  unfold orderedPairSum
  conv_lhs => rw [Finset.sum_range_succ]
  have hlast : (∑ u ∈ Finset.range (h+1), if h<u then A (offset+h) (offset+u) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [ite_eq_right (by have := Finset.mem_range.mp hu; omega)]
  rw [hlast,add_zero]
  have hinner : (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range (h+1),
      if t<u then A (offset+t) (offset+u) else 0) =
      ∑ t ∈ Finset.range h, ((∑ u ∈ Finset.range h,
        if t<u then A (offset+t) (offset+u) else 0)+A (offset+t) (offset+h)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_range_succ,ite_eq_left (Finset.mem_range.mp ht)]
  rw [hinner,Finset.sum_add_distrib]

theorem symmetric_double_sum (A : ℕ → ℕ → ℝ) (hA : ∀ t u, A t u=A u t) (h : ℕ) :
    (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, A t u) =
      (∑ t ∈ Finset.range h, A t t)+2*orderedPairSum A 0 h := by
  induction h with
  | zero => simp [orderedPairSum]
  | succ h ih =>
    have hstep : (∑ t ∈ Finset.range (h+1), ∑ u ∈ Finset.range (h+1), A t u) =
        (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, A t u)+
          2*(∑ t ∈ Finset.range h, A t h)+A h h := by
      rw [Finset.sum_range_succ]
      have hfirst : (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range (h+1), A t u) =
          (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, A t u)+(∑ t ∈ Finset.range h, A t h) := by
        simp_rw [Finset.sum_range_succ]
        rw [Finset.sum_add_distrib]
      rw [hfirst,Finset.sum_range_succ]
      have hcross : (∑ u ∈ Finset.range h, A h u) = ∑ t ∈ Finset.range h, A t h := by
        exact Finset.sum_congr rfl (fun t _ ↦ hA h t)
      rw [hcross]
      ring
    rw [hstep,ih,Finset.sum_range_succ,orderedPairSum_succ]
    simp only [Nat.zero_add]
    ring

theorem square_sum_eq_diagonal_pairs (y : ℕ → ℝ) (offset h : ℕ) :
    (∑ t ∈ Finset.range h, y (offset+t))^2 =
      (∑ t ∈ Finset.range h, y (offset+t)^2)+
        2*orderedPairSum (fun t u ↦ y t*y u) offset h := by
  have hprod : (∑ t ∈ Finset.range h, y (offset+t))^2 =
      ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, y (offset+t)*y (offset+u) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    exact Finset.mul_sum (Finset.range h) (fun u ↦ y (offset+u)) (y (offset+t))
  rw [hprod]
  have hs := symmetric_double_sum (fun t u ↦ y (offset+t)*y (offset+u))
    (fun t u ↦ mul_comm _ _) h
  simpa only [orderedPairSum,Nat.zero_add,pow_two] using hs

theorem chunkSum_add (q r : ℕ → ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSum (fun start n ↦ q start n+r start n) offset ns = chunkSum q offset ns+chunkSum r offset ns := by
  induction ns generalizing offset with
  | nil => simp [chunkSum]
  | cons n ns ih =>
    simp only [chunkSum,ih]
    ring

theorem chunkSum_const_mul (c : ℝ) (q : ℕ → ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSum (fun start n ↦ c*q start n) offset ns = c*chunkSum q offset ns := by
  induction ns generalizing offset with
  | nil => simp [chunkSum]
  | cons n ns ih =>
    simp only [chunkSum,ih]
    ring

theorem chunkSum_diagonal (f : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSum (fun start n ↦ ∑ t ∈ Finset.range (n+1), f (start+t)) offset ns =
      ∑ t ∈ Finset.range (totalRounds ns), f (offset+t) := by
  induction ns generalizing offset with
  | nil => simp [chunkSum,totalRounds]
  | cons n ns ih =>
    change (∑ t ∈ Finset.range (n+1), f (offset+t))+
      chunkSum (fun start k ↦ ∑ t ∈ Finset.range (k+1), f (start+t)) (offset+(n+1)) ns =
        ∑ t ∈ Finset.range ((n+1)+totalRounds ns), f (offset+t)
    rw [ih]
    conv_rhs => rw [Finset.sum_range_add]
    simp only [Nat.add_assoc]

def chunkSquareSum (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  chunkSum (fun start n ↦ (∑ t ∈ Finset.range (n+1), y (start+t))^2) offset ns

theorem chunkSquareSum_nonneg (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    0 ≤ chunkSquareSum y offset ns := by
  induction ns generalizing offset with
  | nil => exact le_rfl
  | cons n ns ih => exact add_nonneg (sq_nonneg _) (ih (offset+(n+1)))

theorem chunkSquareSum_eq_diagonal_pairs (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSquareSum y offset ns = (∑ t ∈ Finset.range (totalRounds ns), y (offset+t)^2)+
      2*chunkSum (fun start n ↦ orderedPairSum (fun t u ↦ y t*y u) start (n+1)) offset ns := by
  have heq : (fun start n ↦ (∑ t ∈ Finset.range (n+1), y (start+t))^2) =
      (fun start n ↦ (∑ t ∈ Finset.range (n+1), y (start+t)^2)+
        2*orderedPairSum (fun t u ↦ y t*y u) start (n+1)) := by
    funext start n
    exact square_sum_eq_diagonal_pairs y start (n+1)
  unfold chunkSquareSum
  rw [heq,chunkSum_add,chunkSum_const_mul,chunkSum_diagonal (fun t ↦ y t^2) offset ns]

end
end Tournament.Restarts
