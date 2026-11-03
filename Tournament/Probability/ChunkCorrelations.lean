module

public import Tournament.Probability.GeometricPartition

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace GeometricPartition

theorem quadratic_eq_diagonal_ordered (r : ℝ) (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic r y offset h=(∑ t ∈ Finset.range h, y (offset+t)^2)+
      2*Restarts.orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) offset h := by
  have hp : Restarts.orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) offset h=
      ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
        if t<u then r^(u-t)*y (offset+t)*y (offset+u) else 0 := by
    unfold Restarts.orderedPairSum
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    dsimp only
    have hd : (offset+u)-(offset+t)=u-t := by omega
    rw [hd]
  rw [hp,quadratic_eq_diagonal_pairs]

end GeometricPartition

namespace Restarts

theorem chunkSum_quadratic (r : ℝ) (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkSum (fun start n ↦ GeometricPartition.quadratic r y start (n+1)) offset ns=
      (∑ t ∈ Finset.range (totalRounds ns), y (offset+t)^2)+
        2*chunkSum (fun start n ↦ orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) start (n+1)) offset ns := by
  have hfun : (fun start n ↦ GeometricPartition.quadratic r y start (n+1))=
      (fun start n ↦ (∑ t ∈ Finset.range (n+1), y (start+t)^2)+
        2*orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) start (n+1)) := by
    funext start n
    exact GeometricPartition.quadratic_eq_diagonal_ordered r y start (n+1)
  rw [hfun,chunkSum_add,chunkSum_const_mul,chunkSum_diagonal (fun t ↦ y t^2) offset ns]

theorem mean_chunkQuadratic {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (r : ℝ) (y : ℕ → ℝ) (offset n : ℕ) :
    (law τ hτ hτ1 n).mean (fun coins ↦
      chunkSum (fun start k ↦ GeometricPartition.quadratic r y start (k+1)) offset (parts n coins))=
        GeometricPartition.quadratic ((1-τ)*r) y offset (n+1) := by
  have hfun : (fun coins : Coins n ↦
      chunkSum (fun start k ↦ GeometricPartition.quadratic r y start (k+1)) offset (parts n coins))=
      (fun coins ↦ (∑ t ∈ Finset.range (n+1), y (offset+t)^2)+
        2*chunkSum (fun start k ↦ orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) start (k+1)) offset (parts n coins)) := by
    funext coins
    rw [chunkSum_quadratic,parts_totalRounds]
  rw [hfun,ProbabilityVector.mean_add,ProbabilityVector.mean_const,ProbabilityVector.mean_const_mul]
  change (∑ t ∈ Finset.range (n+1), y (offset+t)^2)+
    2*chunkSumMean τ hτ hτ1 (fun start k ↦ orderedPairSum (fun t u ↦ r^(u-t)*y t*y u) start (k+1)) n offset=_
  rw [chunkSumMean_orderedPairSum,GeometricPartition.quadratic_eq_diagonal_pairs]
  congr 2
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  have hd : (offset+u)-(offset+t)=u-t := by omega
  rw [hd]
  by_cases htu : t<u
  · rw [ite_eq_left htu,ite_eq_left htu,mul_pow]
    ring
  · rw [ite_eq_right htu,ite_eq_right htu]

end Restarts
end
end Tournament
