module

public import Tournament.Probability.ChunkSums
public import Tournament.Probability.ChunkMembership

@[expose] public section

namespace Tournament.Restarts

open scoped BigOperators Classical

noncomputable section

def orderedPairSum (A : ℕ → ℕ → ℝ) (offset h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
    if t<u then A (offset+t) (offset+u) else 0

def sameChunkPairSum (A : ℕ → ℕ → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  ∑ t ∈ Finset.range (totalRounds ns), ∑ u ∈ Finset.range (totalRounds ns),
    if t<u ∧ chunkIndex ns t=chunkIndex ns u then A (offset+t) (offset+u) else 0

theorem sameChunkPairSum_cons (A : ℕ → ℕ → ℝ) (offset n : ℕ) (ns : List ℕ) :
    sameChunkPairSum A offset (n::ns) = orderedPairSum A offset (n+1)+
      sameChunkPairSum A (offset+(n+1)) ns := by
  unfold sameChunkPairSum orderedPairSum
  change (∑ t ∈ Finset.range ((n+1)+totalRounds ns),
    ∑ u ∈ Finset.range ((n+1)+totalRounds ns),
      if t<u ∧ chunkIndex (n::ns) t=chunkIndex (n::ns) u then A (offset+t) (offset+u) else 0) = _
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [Finset.sum_range_add]
    have hhead : (∑ u ∈ Finset.range (n+1),
        if t<u ∧ chunkIndex (n::ns) t=chunkIndex (n::ns) u then A (offset+t) (offset+u) else 0) =
        ∑ u ∈ Finset.range (n+1), if t<u then A (offset+t) (offset+u) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [chunkIndex,ite_eq_left ht',ite_eq_left (Finset.mem_range.mp hu),and_true]
    have htail : (∑ u ∈ Finset.range (totalRounds ns),
        if t<(n+1)+u ∧ chunkIndex (n::ns) t=chunkIndex (n::ns) ((n+1)+u)
          then A (offset+t) (offset+((n+1)+u)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      have hu : ¬ (n+1)+u<n+1 := by omega
      simp only [chunkIndex,ite_eq_left ht',ite_eq_right hu,Nat.add_sub_cancel_left]
      rw [ite_eq_right (by omega)]
    rw [hhead,htail,add_zero]
  · apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_range_add]
    have hhead : (∑ u ∈ Finset.range (n+1),
        if (n+1)+t<u ∧ chunkIndex (n::ns) ((n+1)+t)=chunkIndex (n::ns) u
          then A (offset+((n+1)+t)) (offset+u) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [ite_eq_right (by have := Finset.mem_range.mp hu; omega)]
    rw [hhead,zero_add]
    apply Finset.sum_congr rfl
    intro u _
    have ht : ¬ (n+1)+t<n+1 := by omega
    have hu : ¬ (n+1)+u<n+1 := by omega
    have hti : chunkIndex (n::ns) ((n+1)+t)=1+chunkIndex ns t := by
      rw [chunkIndex,ite_eq_right ht,Nat.add_sub_cancel_left]
    have hui : chunkIndex (n::ns) ((n+1)+u)=1+chunkIndex ns u := by
      rw [chunkIndex,ite_eq_right hu,Nat.add_sub_cancel_left]
    rw [hti,hui]
    simp only [Nat.add_left_cancel_iff,Nat.add_lt_add_iff_left,Nat.add_assoc]

theorem chunkSum_orderedPairSum (A : ℕ → ℕ → ℝ) (ns : List ℕ) (offset : ℕ) :
    chunkSum (fun start n ↦ orderedPairSum A start (n+1)) offset ns =
      sameChunkPairSum A offset ns := by
  induction ns generalizing offset with
  | nil => simp [chunkSum,sameChunkPairSum,totalRounds]
  | cons n ns ih =>
    change orderedPairSum A offset (n+1)+
      chunkSum (fun start k ↦ orderedPairSum A start (k+1)) (offset+(n+1)) ns = _
    rw [ih,sameChunkPairSum_cons]

theorem chunkSumMean_orderedPairSum {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (A : ℕ → ℕ → ℝ) (n offset : ℕ) :
    chunkSumMean τ hτ hτ1 (fun start k ↦ orderedPairSum A start (k+1)) n offset =
      ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        if t<u then (1-τ)^(u-t)*A (offset+t) (offset+u) else 0 := by
  unfold chunkSumMean
  have heq : (fun coins : Coins n ↦ chunkSum (fun start k ↦ orderedPairSum A start (k+1)) offset (parts n coins)) =
      (fun coins ↦ ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        if t<u ∧ chunkIndex (parts n coins) t=chunkIndex (parts n coins) u
          then A (offset+t) (offset+u) else 0) := by
    funext coins
    rw [chunkSum_orderedPairSum]
    unfold sameChunkPairSum
    rw [parts_totalRounds]
  rw [heq,ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases htu : t<u
  · simp only [htu,true_and,ite_true]
    have hscalar : (law τ hτ hτ1 n).mean (fun coins : Coins n ↦
        if chunkIndex (parts n coins) t=chunkIndex (parts n coins) u then A (offset+t) (offset+u) else 0) =
        (law τ hτ hτ1 n).probability (fun coins ↦ chunkIndex (parts n coins) t=chunkIndex (parts n coins) u)*
          A (offset+t) (offset+u) := by
      rw [ProbabilityVector.probability,← ProbabilityVector.mean_mul_const]
      apply congrArg (ProbabilityVector.mean _)
      funext coins
      by_cases hi : chunkIndex (parts n coins) t=chunkIndex (parts n coins) u
      · simp only [ite_eq_left hi,one_mul]
      · simp only [ite_eq_right hi,zero_mul]
    rw [hscalar,same_chunk_probability hτ hτ1 n t u (Nat.le_of_lt htu)
      (by have := Finset.mem_range.mp hu; omega)]
  · simp only [htu,false_and,ite_false,ProbabilityVector.mean_const]

end
end Tournament.Restarts
