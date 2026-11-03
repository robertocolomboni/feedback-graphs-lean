module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open scoped Classical BigOperators
noncomputable section

def cumulative (d : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t∈Finset.range n, d t

theorem prefix_zero (d : ℕ → ℝ) : cumulative d 0=0 := by simp [cumulative]

theorem prefix_succ (d : ℕ → ℝ) (t : ℕ) : cumulative d (t+1)=cumulative d t+d t := by
  simp only [cumulative,Finset.sum_range_succ]

def futurePeak (D : ℕ → ℝ) (s : ℕ) : ℕ → ℝ
  | 0 => D s
  | n+1 => max (D s) (futurePeak D (s+1) n)

theorem le_futurePeak (D : ℕ → ℝ) (s n : ℕ) : D s≤futurePeak D s n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem futurePeak_lt_iff (D : ℕ → ℝ) (s n : ℕ) (x : ℝ) :
    futurePeak D s n<x ↔ ∀ r≤n, D (s+r)<x := by
  induction n generalizing s with
  | zero => simp [futurePeak]
  | succ n ih =>
    rw [futurePeak,max_lt_iff,ih]
    constructor
    · rintro ⟨hs,hr⟩ r hR
      cases r with
      | zero => simpa only [Nat.add_zero] using hs
      | succ r =>
        have h := hr r (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · intro h
      constructor
      · simpa only [Nat.add_zero] using h 0 (by omega)
      · intro r hr
        have h' := h (r+1) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h'

def suffixMax (d : ℕ → ℝ) (T t : ℕ) : ℝ := futurePeak (cumulative d) t (T-t)

def Terminal (d : ℕ → ℝ) (T t : ℕ) : Prop := suffixMax d T (t+1)<cumulative d t

theorem prefix_le_suffix (d : ℕ → ℝ) (T t : ℕ) : cumulative d t≤suffixMax d T t :=
  le_futurePeak _ _ _

theorem suffixMax_succ (d : ℕ → ℝ) (T t : ℕ) (ht : t<T) :
    suffixMax d T t=max (cumulative d t) (suffixMax d T (t+1)) := by
  have hn : T-t=(T-(t+1))+1 := by omega
  unfold suffixMax
  rw [hn,futurePeak]

theorem terminal_iff (d : ℕ → ℝ) (T t : ℕ) (ht : t<T) :
    Terminal d T t ↔ ∀ u, t<u → u≤T → cumulative d u<cumulative d t := by
  rw [Terminal,suffixMax,futurePeak_lt_iff]
  constructor
  · intro h u htu huT
    have hr : u-(t+1)≤T-(t+1) := by omega
    have h' := h (u-(t+1)) hr
    have hEq : t+1+(u-(t+1))=u := by omega
    simpa only [hEq] using h'
  · intro h r hr
    exact h (t+1+r) (by omega) (by omega)

theorem suffix_drop_le (d : ℕ → ℝ) (T t : ℕ) (ht : t<T) (hdt : -1≤d t) :
    suffixMax d T t-suffixMax d T (t+1)≤if Terminal d T t then (1:ℝ) else 0 := by
  by_cases h : Terminal d T t
  · have hp : suffixMax d T (t+1)<cumulative d t := h
    rw [ite_eq_left h,suffixMax_succ d T t ht,max_eq_left hp.le]
    have hNext := prefix_le_suffix d T (t+1)
    rw [prefix_succ] at hNext
    linarith
  · have hp : cumulative d t≤suffixMax d T (t+1) := le_of_not_gt h
    rw [ite_eq_right h,suffixMax_succ d T t ht,max_eq_right hp,sub_self]

theorem telescope_drops (F : ℕ → ℝ) (s : ℕ) :
    (∑ t∈Finset.range s, (F t-F (t+1)))=F 0-F s := by
  induction s with
  | zero => simp
  | succ s ih => rw [Finset.sum_range_succ,ih]; ring

def terminalCount (d : ℕ → ℝ) (T s : ℕ) : ℕ := ((Finset.range s).filter (Terminal d T)).card

theorem terminalCount_eq_sum (d : ℕ → ℝ) (T s : ℕ) :
    (terminalCount d T s:ℝ)=∑ t∈Finset.range s, if Terminal d T t then (1:ℝ) else 0 := by
  simp only [terminalCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem negative_prefix_le_count_of_boundary (d : ℕ → ℝ) (T s : ℕ) (hs : s≤T)
    (hd : ∀ t<T, -1≤d t) (hBoundary : suffixMax d T s=cumulative d s) :
    -cumulative d s≤(terminalCount d T s:ℝ) := by
  have hZero : 0≤suffixMax d T 0 := by simpa only [prefix_zero] using prefix_le_suffix d T 0
  have hDrops := Finset.sum_le_sum (s := Finset.range s) (fun t ht ↦
    suffix_drop_le d T t (by have := Finset.mem_range.mp ht; omega)
      (hd t (by have := Finset.mem_range.mp ht; omega)))
  rw [telescope_drops,← terminalCount_eq_sum,hBoundary] at hDrops
  linarith

theorem suffixMax_last (d : ℕ → ℝ) (T : ℕ) : suffixMax d T T=cumulative d T := by
  simp only [suffixMax,Nat.sub_self,futurePeak]

theorem suffixMax_at_terminal (d : ℕ → ℝ) (T s : ℕ) (hs : s<T) (h : Terminal d T s) :
    suffixMax d T s=cumulative d s := by
  rw [suffixMax_succ d T s hs,max_eq_left (le_of_lt h)]

theorem negative_prefix_le_terminal_count (d : ℕ → ℝ) (T s : ℕ) (hs : s≤T)
    (hd : ∀ t<T, -1≤d t) (hStop : s=T ∨ Terminal d T s) :
    -cumulative d s≤(terminalCount d T s:ℝ) := by
  apply negative_prefix_le_count_of_boundary d T s hs hd
  rcases hStop with hEq | h
  · rw [hEq]
    exact suffixMax_last d T
  · by_cases hEq : s=T
    · simpa only [hEq] using suffixMax_last d T
    · exact suffixMax_at_terminal d T s (by omega) h

end
end Tournament.Upper.GeometricProbing
