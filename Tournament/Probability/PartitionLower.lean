module

public import Tournament.Probability.GeometricPartition
public import Tournament.Probability.RestartCount

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω : Type*} [Fintype Ω]

theorem mean_div_const (μ : ProbabilityVector Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun x ↦ f x/c) = μ.mean f/c := by
  simp only [div_eq_mul_inv,mean_mul_const]

theorem reciprocal_mean_le_mean_reciprocal (μ : ProbabilityVector Ω) (k : Ω → ℝ)
    (hk : ∀ x, 1 ≤ k x) :
    1/μ.mean k ≤ μ.mean (fun x ↦ 1/k x) := by
  let m := μ.mean k
  have hm : 1 ≤ m := by
    calc
      1 = μ.mean (fun _ ↦ 1) := (mean_const μ 1).symm
      _ ≤ μ.mean k := mean_mono μ hk
  have hm0 : 0 < m := by linarith
  have htangent : ∀ x, 2/m-k x/m^2 ≤ 1/k x := by
    intro x
    have hk0 : 0 < k x := by linarith [hk x]
    have hid : 1/k x-(2/m-k x/m^2) = (k x-m)^2/(k x*m^2) := by
      field_simp [ne_of_gt hk0,ne_of_gt hm0]
      ring
    have hright : 0 ≤ (k x-m)^2/(k x*m^2) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hk0 (sq_pos_of_pos hm0)))
    rw [← hid] at hright
    linarith
  have ht := mean_mono μ htangent
  rw [mean_sub,mean_const,mean_div_const] at ht
  have hmean : μ.mean k=m := rfl
  rw [hmean] at ht
  have hid : 2/m-m/m^2=1/m := by
    field_simp [ne_of_gt hm0]
    ring
  rwa [hid] at ht

end ProbabilityVector

namespace Restarts

theorem chunkSquareSum_centering_nonneg (y : ℕ → ℝ) (offset : ℕ) (ns : List ℕ) (c : ℝ) :
    0 ≤ chunkSquareSum y offset ns -2*c*(∑ t ∈ Finset.range (totalRounds ns), y (offset+t))+
      (ns.length:ℝ)*c^2 := by
  induction ns generalizing offset with
  | nil => simp [chunkSquareSum,chunkSum,totalRounds]
  | cons n ns ih =>
    have hs : (∑ t ∈ Finset.range (totalRounds (n::ns)), y (offset+t)) =
        (∑ t ∈ Finset.range (n+1), y (offset+t))+
          ∑ t ∈ Finset.range (totalRounds ns), y ((offset+(n+1))+t) := by
      change (∑ t ∈ Finset.range ((n+1)+totalRounds ns), y (offset+t)) = _
      rw [Finset.sum_range_add]
      simp only [Nat.add_assoc]
    have htail := ih (offset+(n+1))
    rw [hs,List.length_cons,Nat.cast_add,Nat.cast_one]
    change 0 ≤ ((∑ t ∈ Finset.range (n+1), y (offset+t))^2+chunkSquareSum y (offset+(n+1)) ns)-
      2*c*((∑ t ∈ Finset.range (n+1), y (offset+t))+
        ∑ t ∈ Finset.range (totalRounds ns), y ((offset+(n+1))+t))+
          ((ns.length:ℝ)+1)*c^2
    nlinarith [sq_nonneg ((∑ t ∈ Finset.range (n+1), y (offset+t))-c)]

theorem square_total_div_count_le_chunkSquares (y : ℕ → ℝ) (offset : ℕ)
    (ns : List ℕ) (hns : ns ≠ []) :
    (∑ t ∈ Finset.range (totalRounds ns), y (offset+t))^2/(ns.length:ℝ) ≤ chunkSquareSum y offset ns := by
  let s := ∑ t ∈ Finset.range (totalRounds ns), y (offset+t)
  let k : ℝ := ns.length
  have hk : 0 < k := by
    change 0 < (ns.length:ℝ)
    exact_mod_cast List.length_pos_iff.mpr hns
  have hc := chunkSquareSum_centering_nonneg y offset ns (s/k)
  change 0 ≤ chunkSquareSum y offset ns-2*(s/k)*s+k*(s/k)^2 at hc
  have hid : chunkSquareSum y offset ns-2*(s/k)*s+k*(s/k)^2 = chunkSquareSum y offset ns-s^2/k := by
    field_simp [ne_of_gt hk]
    ring
  rw [hid] at hc
  linarith

theorem expected_intervalCount {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (law τ hτ hτ1 n).mean (fun coins ↦ ((parts n coins).length:ℝ)) = 1+(n:ℝ)*τ := by
  have heq : (fun coins : Coins n ↦ ((parts n coins).length:ℝ)) =
      (fun coins ↦ 1+(restartCount n coins:ℝ)) := by
    funext coins
    have hnat := parts_boundary_count n coins
    have hne := parts_nonempty n coins
    have hlen := List.length_pos_iff.mpr hne
    have hlen_eq : (parts n coins).length=1+restartCount n coins := by omega
    rw [hlen_eq,Nat.cast_add,Nat.cast_one]
  rw [heq,ProbabilityVector.mean_add,ProbabilityVector.mean_const,expected_restartCount]

end Restarts

namespace GeometricPartition

theorem constant_vector_lower {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (y : ℕ → ℝ) (offset n : ℕ) :
    (∑ t ∈ Finset.range (n+1), y (offset+t))^2/(1+(1-χ)*(n:ℝ)) ≤ quadratic χ y offset (n+1) := by
  let μ := Restarts.law (1-χ) (sub_nonneg.mpr hχ1) (by linarith) n
  let k : Restarts.Coins n → ℝ := fun coins ↦ (Restarts.parts n coins).length
  let s := ∑ t ∈ Finset.range (n+1), y (offset+t)
  have hk : ∀ coins, 1 ≤ k coins := by
    intro coins
    change 1 ≤ ((Restarts.parts n coins).length:ℝ)
    have hlen : 1 ≤ (Restarts.parts n coins).length :=
      Nat.succ_le_iff.mpr (List.length_pos_iff.mpr (Restarts.parts_nonempty n coins))
    exact_mod_cast hlen
  have hJ := ProbabilityVector.reciprocal_mean_le_mean_reciprocal μ k hk
  have hcount : μ.mean k=1+(1-χ)*(n:ℝ) := by
    have hc := Restarts.expected_intervalCount (sub_nonneg.mpr hχ1) (by linarith : 1-χ ≤ 1) n
    change μ.mean k=1+(n:ℝ)*(1-χ) at hc
    nlinarith
  have hpoint : ∀ coins, s^2/k coins ≤ Restarts.chunkSquareSum y offset (Restarts.parts n coins) := by
    intro coins
    have h := Restarts.square_total_div_count_le_chunkSquares y offset (Restarts.parts n coins)
      (Restarts.parts_nonempty n coins)
    rw [Restarts.parts_totalRounds] at h
    exact h
  have hCS := ProbabilityVector.mean_mono μ hpoint
  rw [quadratic_eq_mean_chunkSquares hχ hχ1]
  change s^2/(1+(1-χ)*(n:ℝ)) ≤ μ.mean (fun coins ↦ Restarts.chunkSquareSum y offset (Restarts.parts n coins))
  have hmul := mul_le_mul_of_nonneg_left hJ (sq_nonneg s)
  rw [hcount] at hmul
  have hlinear : μ.mean (fun coins ↦ s^2/k coins)=s^2*μ.mean (fun coins ↦ 1/k coins) := by
    simp only [div_eq_mul_inv,one_mul,ProbabilityVector.mean_const_mul]
  rw [hlinear] at hCS
  simpa only [div_eq_mul_inv,one_mul] using le_trans hmul hCS

end GeometricPartition
end
end Tournament
