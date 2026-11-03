module

public import Tournament.Probability.DyadicRate

@[expose] public section

namespace Tournament.DyadicRate

open scoped BigOperators Classical

noncomputable section

theorem shifted_weight (m d : ℕ) (j : Fin (m+1))
    (hjd : j.val+d<m) :
    weight m j=(2:ℝ)^d*weight m ⟨j.val+d,by omega⟩ := by
  have hj : j.val<m := by omega
  simp only [weight,ite_eq_left hj,ite_eq_left hjd]
  have hp : (1/2:ℝ)^(j.val+d+1)=(1/2:ℝ)^(j.val+1)*(1/2:ℝ)^d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  have hone : (2:ℝ)^d*(1/2:ℝ)^d=1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (1/2:ℝ)^(j.val+1)*((2:ℝ)^d*(1/2:ℝ)^d) := by rw [hone,mul_one]
    _ = _ := by ring

theorem tail_weight_sum (m s : ℕ) (hs : s≤m) :
    (∑ j : Fin (m+1), if s≤j.val then weight m j else 0)=(1/2:ℝ)^s := by
  let f : ℕ → ℝ := fun j ↦ if s≤j then
    (if j<m then (1/2:ℝ)^(j+1) else (1/2:ℝ)^m) else 0
  change (∑ j : Fin (m+1), f j.val)=_
  rw [Fin.sum_univ_eq_sum_range f]
  have hsplit := Finset.sum_range_add f s (m-s+1)
  have hN : s+(m-s+1)=m+1 := by omega
  rw [hN] at hsplit
  have hprefix : (∑ j ∈ Finset.range s, f j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (by have := Finset.mem_range.mp hj; omega)
  rw [hsplit,hprefix,zero_add,Finset.sum_range_succ]
  have hfirst : (∑ j ∈ Finset.range (m-s), f (s+j))=
      (1/2:ℝ)^s*(∑ j ∈ Finset.range (m-s), (1/2:ℝ)^(j+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hsj : s+j<m := by have := Finset.mem_range.mp hj; omega
    simp only [f,ite_eq_left (show s≤s+j by omega),ite_eq_left hsj]
    rw [← pow_add]
    congr 1
  have hlast : f (s+(m-s))=(1/2:ℝ)^s*(1/2:ℝ)^(m-s) := by
    have hsm : s+(m-s)=m := Nat.add_sub_of_le hs
    simp only [hsm,f,ite_eq_left hs,lt_self_iff_false,ite_false]
    rw [← pow_add,hsm]
  rw [hfirst,hlast,← mul_add]
  have hg := geometric_partition (m-s)
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (1/2:ℝ)^(j+1))] at hg
  rw [hg,mul_one]

theorem tail_probability (m s : ℕ) (hs : s≤m) :
    (law m).mean (fun j ↦ if s≤j.val then 1 else 0)=(1/2:ℝ)^s := by
  change (∑ j : Fin (m+1), weight m j*(if s≤j.val then 1 else 0))=_
  simp only [mul_ite,mul_one,mul_zero]
  exact tail_weight_sum m s hs

end
end Tournament.DyadicRate
