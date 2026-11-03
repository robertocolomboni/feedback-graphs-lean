module

public import Tournament.Probability.PartitionRowBound

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace FiniteGrouping

def total (index : ℕ → ℕ) (y : ℕ → ℝ) (h j : ℕ) : ℝ :=
  ∑ t ∈ Finset.range h, if index t=j then y t else 0

theorem weighted_sum (index : ℕ → ℕ) (y : ℕ → ℝ) (h k : ℕ)
    (hi : ∀ t, t<h → index t<k) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range k, f j*total index y h j) =
      ∑ t ∈ Finset.range h, f (index t)*y t := by
  unfold total
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hit : index t ∈ Finset.range k := Finset.mem_range.mpr (hi t (Finset.mem_range.mp ht))
  calc
    _ = f (index t)*(if index t=index t then y t else 0) := by
      apply Finset.sum_eq_single_of_mem (index t) hit
      intro j _ hj
      rw [ite_eq_right (Ne.symm hj),mul_zero]
    _ = _ := by rw [ite_eq_left rfl]

theorem quadratic_pullback (index : ℕ → ℕ) (y : ℕ → ℝ) (h k : ℕ)
    (hi : ∀ t, t<h → index t<k) (A : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range k, ∑ l ∈ Finset.range k,
      A j l*total index y h j*total index y h l) =
        ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, A (index t) (index u)*y t*y u := by
  calc
    _ = ∑ j ∈ Finset.range k, (∑ l ∈ Finset.range k, A j l*total index y h l)*total index y h j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ t ∈ Finset.range h, (∑ l ∈ Finset.range k, A (index t) l*total index y h l)*y t :=
      weighted_sum index y h k hi _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [weighted_sum index y h k hi,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      ring

end FiniteGrouping

namespace Restarts

theorem chunkIndex_lt_length (ns : List ℕ) (t : ℕ) (ht : t<totalRounds ns) :
    chunkIndex ns t<ns.length := by
  induction ns generalizing t with
  | nil => simp only [totalRounds] at ht; omega
  | cons n ns ih =>
    by_cases hhead : t<n+1
    · rw [chunkIndex,ite_eq_left hhead,List.length_cons]
      omega
    · rw [chunkIndex,ite_eq_right hhead,List.length_cons]
      have htail : t-(n+1)<totalRounds ns := by
        change t<(n+1)+totalRounds ns at ht
        omega
      have h := ih (t-(n+1)) htail
      omega

def chunkTotal (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) (j : ℕ) : ℝ :=
  FiniteGrouping.total (chunkIndex ns) (fun t ↦ y (offset+t)) (totalRounds ns) j

theorem chunkTotal_cons_zero (y : ℕ → ℝ) (offset n : ℕ) (ns : List ℕ) :
    chunkTotal y offset (n::ns) 0 = ∑ t ∈ Finset.range (n+1), y (offset+t) := by
  unfold chunkTotal FiniteGrouping.total
  change (∑ t ∈ Finset.range ((n+1)+totalRounds ns),
    if chunkIndex (n::ns) t=0 then y (offset+t) else 0) = _
  rw [Finset.sum_range_add]
  have hhead : (∑ t ∈ Finset.range (n+1), if chunkIndex (n::ns) t=0 then y (offset+t) else 0) =
      ∑ t ∈ Finset.range (n+1), y (offset+t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [chunkIndex,ite_eq_left (Finset.mem_range.mp ht),ite_eq_left rfl]
  have htail : (∑ t ∈ Finset.range (totalRounds ns),
      if chunkIndex (n::ns) ((n+1)+t)=0 then y (offset+((n+1)+t)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have hindex : chunkIndex (n::ns) ((n+1)+t)=1+chunkIndex ns t := by
      rw [chunkIndex,ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rw [hindex,ite_eq_right (by omega)]
  rw [hhead,htail,add_zero]

theorem chunkTotal_cons_succ (y : ℕ → ℝ) (offset n : ℕ) (ns : List ℕ) (j : ℕ) :
    chunkTotal y offset (n::ns) (j+1) = chunkTotal y (offset+(n+1)) ns j := by
  unfold chunkTotal FiniteGrouping.total
  change (∑ t ∈ Finset.range ((n+1)+totalRounds ns),
    if chunkIndex (n::ns) t=j+1 then y (offset+t) else 0) = _
  rw [Finset.sum_range_add]
  have hhead : (∑ t ∈ Finset.range (n+1), if chunkIndex (n::ns) t=j+1 then y (offset+t) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [chunkIndex,ite_eq_left (Finset.mem_range.mp ht),ite_eq_right (by omega)]
  rw [hhead,zero_add]
  apply Finset.sum_congr rfl
  intro t _
  have hindex : chunkIndex (n::ns) ((n+1)+t)=1+chunkIndex ns t := by
    rw [chunkIndex,ite_eq_right (by omega),Nat.add_sub_cancel_left]
  rw [hindex]
  have heq : 1+chunkIndex ns t=j+1 ↔ chunkIndex ns t=j := by omega
  simp only [heq,Nat.add_assoc]

theorem chunkSquareSum_eq_sum_chunkTotal_sq (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSquareSum y offset ns = ∑ j ∈ Finset.range ns.length, chunkTotal y offset ns j^2 := by
  induction ns generalizing offset with
  | nil => simp [chunkSquareSum,chunkSum]
  | cons n ns ih =>
    change (∑ t ∈ Finset.range (n+1), y (offset+t))^2+chunkSquareSum y (offset+(n+1)) ns = _
    rw [List.length_cons]
    conv_rhs => rw [Finset.sum_range_succ']
    rw [chunkTotal_cons_zero,ih]
    have htail : (∑ j ∈ Finset.range ns.length, chunkTotal y offset (n::ns) (j+1)^2) =
        ∑ j ∈ Finset.range ns.length, chunkTotal y (offset+(n+1)) ns j^2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [chunkTotal_cons_succ]
    rw [htail]
    ring

end Restarts

namespace GeometricPartition

def compressedQuadratic (r : ℝ) (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  quadratic r (Restarts.chunkTotal y offset ns) 0 ns.length

theorem compressedQuadratic_pullback (r : ℝ) (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    compressedQuadratic r y offset ns =
      ∑ t ∈ Finset.range (Restarts.totalRounds ns), ∑ u ∈ Finset.range (Restarts.totalRounds ns),
        r^(Nat.dist (Restarts.chunkIndex ns t) (Restarts.chunkIndex ns u))*y (offset+t)*y (offset+u) := by
  have h := FiniteGrouping.quadratic_pullback (Restarts.chunkIndex ns) (fun t ↦ y (offset+t))
    (Restarts.totalRounds ns) ns.length (fun t ht ↦ Restarts.chunkIndex_lt_length ns t ht)
      (fun j l ↦ r^(Nat.dist j l))
  simpa only [compressedQuadratic,quadratic,Nat.zero_add,Restarts.chunkTotal] using h

theorem compressedQuadratic_le_chunkSquares {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    compressedQuadratic r y offset ns ≤ (2/(1-r))*Restarts.chunkSquareSum y offset ns := by
  unfold compressedQuadratic
  have h := quadratic_le_diagonal hr hr1 (Restarts.chunkTotal y offset ns) 0 ns.length
  simpa only [Nat.zero_add,Restarts.chunkSquareSum_eq_sum_chunkTotal_sq] using h

end GeometricPartition
end
end Tournament
