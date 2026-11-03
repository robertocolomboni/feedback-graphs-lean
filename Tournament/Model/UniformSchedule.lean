module

public import Tournament.Model.BlockAccounting
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace Tournament.Model.UniformSchedule

open scoped BigOperators Classical

def count (T H : ℕ) : ℕ := T/H+(if T%H=0 then 0 else 1)

def transitions (T H b : ℕ) : ℕ :=
  if b<T/H then H-1 else if T%H=0 then H-1 else T%H-1

theorem length_full (T H b : ℕ) (hH : 0<H) (hb : b<T/H) :
    transitions T H b+1=H := by
  simp only [transitions,ite_eq_left hb]
  omega

theorem length_short (T H : ℕ) (hr : T%H≠0) :
    transitions T H (T/H)+1=T%H := by
  simp only [transitions,lt_self_iff_false,ite_false,ite_eq_right hr]
  omega

theorem length_le (T H b : ℕ) (hH : 0<H) : transitions T H b+1≤H := by
  by_cases hb : b<T/H
  · rw [length_full T H b hH hb]
  · simp only [transitions,ite_eq_right hb]
    by_cases hr : T%H=0
    · simp only [ite_eq_left hr]
      omega
    · simp only [ite_eq_right hr]
      have hmod := Nat.mod_lt T hH
      omega

theorem total (T H : ℕ) (hH : 0<H) :
    prefixHorizon (fun b ↦ transitions T H b+1) (count T H)=T := by
  have hfull : prefixHorizon (fun b ↦ transitions T H b+1) (T/H)=(T/H)*H := by
    unfold prefixHorizon
    calc
      _ = ∑ _b ∈ Finset.range (T/H), H :=
        Finset.sum_congr rfl (fun b hb ↦ length_full T H b hH (Finset.mem_range.mp hb))
      _ = _ := by simp [Nat.mul_comm]
  by_cases hr : T%H=0
  · simp only [count,ite_eq_left hr,Nat.add_zero,hfull]
    simpa only [hr,Nat.zero_add,Nat.mul_comm] using Nat.mod_add_div T H
  · simp only [count,ite_eq_right hr]
    rw [prefixHorizon_succ,hfull,length_short T H hr]
    simpa only [Nat.mul_comm] using Nat.div_add_mod T H

theorem count_mul_le (T H : ℕ) : count T H*H≤T+H := by
  have hd := Nat.div_mul_le_self T H
  unfold count
  split <;> simp only [Nat.add_mul,Nat.zero_mul,Nat.one_mul] <;> omega

theorem count_pos (T H : ℕ) (hT : 0<T) (hH : 0<H) : 0<count T H := by
  by_cases hr : T%H=0
  · simp only [count,ite_eq_left hr,Nat.add_zero]
    exact Nat.div_pos (Nat.le_of_dvd hT (Nat.dvd_of_mod_eq_zero hr)) hH
  · simp only [count,ite_eq_right hr]
    exact Nat.succ_pos _

end Tournament.Model.UniformSchedule
