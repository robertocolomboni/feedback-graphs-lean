module

public import Tournament.Lower.DyadicCongestion
public import Tournament.Model.Regret
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace Tournament.Lower.Dyadic

open scoped BigOperators Classical

noncomputable section

variable {α : Type*} [DecidableEq α]

def changed (I : ℕ → α) (a b : ℕ) : ℕ := if I b=I a then 0 else 1

def boundaryChange (I : ℕ → α) (u : ℕ) : ℕ := changed I (u-1) u

theorem changed_triangle (I : ℕ → α) (a b : ℕ) :
    changed I a (b+1)≤changed I a b+boundaryChange I (b+1) := by
  by_cases hb : I b=I a
  · by_cases hc : I (b+1)=I b
    · simp [changed,boundaryChange,hb,hc]
    · have ha : I (b+1)≠I a := by
        intro hh
        exact hc (hh.trans hb.symm)
      simp [changed,boundaryChange,hb,ha]
  · simp only [boundaryChange,Nat.add_sub_cancel,changed,ite_eq_right hb]
    split_ifs <;> omega

theorem changed_le_interval (I : ℕ → α) (a b : ℕ) (hab : a≤b) :
    changed I a b≤∑ u ∈ Finset.Ioc a b, boundaryChange I u := by
  refine Nat.le_induction ?_ ?_ b hab
  · simp [changed]
  · intro b hab ih
    rw [Finset.sum_Ioc_succ_top hab]
    exact (changed_triangle I a b).trans (Nat.add_le_add_right ih _)

theorem edge_change_le (I : ℕ → α) (T t : ℕ) (ht : 0<t) (htT : t≤T) :
    changed I (parent t) t≤∑ u ∈ Finset.Icc 1 T,
      if parent t<u ∧ u≤t then boundaryChange I u else 0 := by
  have hfilter : (Finset.Icc 1 T).filter (fun u ↦ parent t<u ∧ u≤t)=Finset.Ioc (parent t) t := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter,hfilter]
  exact changed_le_interval I (parent t) t (parent_lt t ht).le

theorem parent_changes_le_boundaries (I : ℕ → α) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, changed I (parent t) t)≤
      bandCount T*(∑ u ∈ Finset.Icc 1 T, boundaryChange I u) := by
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ u ∈ Finset.Icc 1 T,
        if parent t<u ∧ u≤t then boundaryChange I u else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      have h := Finset.mem_Icc.mp ht
      exact edge_change_le I T t (by omega) h.2
    _ = ∑ u ∈ Finset.Icc 1 T, (crossings T u).card*boundaryChange I u := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      simp [crossings]
    _ ≤ ∑ u ∈ Finset.Icc 1 T, bandCount T*boundaryChange I u := by
      apply Finset.sum_le_sum
      intro u _
      exact Nat.mul_le_mul_right (boundaryChange I u) (crossings_card_le T u)
    _ = _ := (Finset.mul_sum _ _ _).symm

def padded (I : ℕ → α) (t : ℕ) : Option α := if t=0 then none else some (I (t-1))

theorem switchCount_succ (I : ℕ → α) (T : ℕ) (hT : 1≤T) :
    Model.switchCount (T+1) I=Model.switchCount T I+boundaryChange I T := by
  have h := Finset.sum_range_succ (fun t ↦ changed I t (t+1)) (T-1)
  simpa only [Model.switchCount,changed,boundaryChange,Nat.add_sub_cancel,Nat.sub_add_cancel hT] using h

theorem padded_boundary_sum (I : ℕ → α) (T : ℕ) (hT : 1≤T) :
    (∑ u ∈ Finset.Icc 1 T, boundaryChange (padded I) u)=Model.switchCount T I+1 := by
  refine Nat.le_induction ?_ ?_ T hT
  · simp [padded,boundaryChange,changed,Model.switchCount]
  · intro T hT ih
    rw [Finset.sum_Icc_succ_top (by omega : 1≤T+1),ih,switchCount_succ I T hT]
    have heq : boundaryChange (padded I) (T+1)=boundaryChange I T := by
      simp [boundaryChange,changed,padded,show T≠0 by omega]
    rw [heq]
    omega

theorem parent_changes_le_switchCount (I : ℕ → α) (T : ℕ) (hT : 1≤T) :
    ((∑ t ∈ Finset.Icc 1 T, changed (padded I) (parent t) t):ℝ)≤
      upsilon T*((Model.switchCount T I:ℝ)+1) := by
  have h := parent_changes_le_boundaries (padded I) T
  rw [padded_boundary_sum I T hT] at h
  have hr : ((∑ t ∈ Finset.Icc 1 T, changed (padded I) (parent t) t):ℝ)≤
      (bandCount T:ℝ)*((Model.switchCount T I:ℝ)+1) := by exact_mod_cast h
  exact hr.trans (mul_le_mul_of_nonneg_right (bandCount_le_upsilon T (by omega)) (by positivity))

end
end Tournament.Lower.Dyadic
