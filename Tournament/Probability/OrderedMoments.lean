module

public import Tournament.Foundations.Centering
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Tournament.OrderedMoments

open scoped BigOperators

noncomputable section

def orderedProducts (y : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k+1, n => ∑ t ∈ Finset.range n, y t * orderedProducts y k (t+1)

theorem orderedProducts_step (y : ℕ → ℝ) (k n : ℕ) :
    orderedProducts y (k+1) (n+1) =
      orderedProducts y (k+1) n + y n * orderedProducts y k (n+1) := by
  simp only [orderedProducts, Finset.sum_range_succ]

theorem orderedProducts_nonneg (y : ℕ → ℝ) (hy : ∀ t, 0 ≤ y t) (k n : ℕ) :
    0 ≤ orderedProducts y k n := by
  induction k generalizing n with
  | zero => exact zero_le_one
  | succ k ih => exact Finset.sum_nonneg (fun t _ ↦ mul_nonneg (hy t) (ih (t+1)))

theorem orderedProducts_one (y : ℕ → ℝ) (n : ℕ) :
    orderedProducts y 1 n = ∑ t ∈ Finset.range n, y t := by
  simp [orderedProducts]

theorem orderedProducts_congr_prefix (y z : ℕ → ℝ) (n : ℕ)
    (h : ∀ t, t<n → y t=z t) (k m : ℕ) (hm : m ≤ n) :
    orderedProducts y k m = orderedProducts z k m := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    apply Finset.sum_congr rfl
    intro t ht
    have htm : t < m := Finset.mem_range.mp ht
    rw [h t (by omega), ih (t+1) (by omega)]

def inclusiveTail (y : ℕ → ℝ) (n s : ℕ) : ℝ :=
  ∑ u ∈ Finset.range n, if s ≤ u then y u else 0

theorem orderedProducts_last_index (y : ℕ → ℝ) (k n : ℕ) :
    orderedProducts y (k+2) n = ∑ s ∈ Finset.range n,
      (y s * orderedProducts y k (s+1)) * inclusiveTail y n s := by
  have hprefix (u : ℕ) (hu : u < n) :
      orderedProducts y (k+1) (u+1) = ∑ s ∈ Finset.range n,
        if s ≤ u then y s * orderedProducts y k (s+1) else 0 := by
    change (∑ s ∈ Finset.range (u+1), y s * orderedProducts y k (s+1)) = _
    have hfilter : (Finset.range n).filter (fun s ↦ s ≤ u) = Finset.range (u+1) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter, hfilter]
  change (∑ u ∈ Finset.range n, y u * orderedProducts y (k+1) (u+1)) = _
  calc
    _ = ∑ u ∈ Finset.range n, ∑ s ∈ Finset.range n,
        y u * (if s ≤ u then y s * orderedProducts y k (s+1) else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hprefix u (Finset.mem_range.mp hu), Finset.mul_sum]
    _ = ∑ s ∈ Finset.range n, ∑ u ∈ Finset.range n,
        y u * (if s ≤ u then y s * orderedProducts y k (s+1) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      unfold inclusiveTail
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      split <;> ring

theorem inclusiveTail_split (y : ℕ → ℝ) (n t : ℕ) (ht : t < n) :
    inclusiveTail y n t = y t + ∑ u ∈ Finset.range n, if t < u then y u else 0 := by
  have heq : (fun u ↦ if t ≤ u then y u else 0) =
      (fun u ↦ (if u=t then y t else 0) + (if t<u then y u else 0)) := by
    funext u
    by_cases hut : u=t
    · subst u
      simp
    · by_cases htu : t < u
      · simp [hut, htu, Nat.le_of_lt htu]
      · have hnot : ¬ t ≤ u := by omega
        simp [hut, htu, hnot]
  unfold inclusiveTail
  rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range.mpr ht, ite_true]

theorem power_increment_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    b^(k+1) ≤ a^(k+1) + ((k:ℝ)+1)*(b-a)*b^k := by
  have hb : 0 ≤ b := le_trans ha hab
  have h := le_trans (le_abs_self (b^(k+1)-a^(k+1)))
    (abs_pow_sub_pow_le (a := b) (b := a) (n := k+1))
  rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg hb, abs_of_nonneg ha,
    max_eq_left hab, Nat.add_sub_cancel] at h
  push_cast at h
  nlinarith

theorem sum_pow_le_factorial_ordered (y : ℕ → ℝ) (hy : ∀ t, 0 ≤ y t) (k n : ℕ) :
    (∑ t ∈ Finset.range n, y t)^k ≤ (Nat.factorial k : ℝ) * orderedProducts y k n := by
  induction k generalizing n with
  | zero => simp [orderedProducts]
  | succ k ih =>
    induction n with
    | zero => simp [orderedProducts]
    | succ n ihn =>
      have hsum : 0 ≤ ∑ t ∈ Finset.range n, y t := Finset.sum_nonneg (fun t _ ↦ hy t)
      have hinc : (∑ t ∈ Finset.range (n+1), y t)^(k+1) ≤
          (∑ t ∈ Finset.range n, y t)^(k+1) +
            (((k:ℝ)+1)*y n) * (∑ t ∈ Finset.range (n+1), y t)^k := by
        have h := power_increment_le hsum (le_add_of_nonneg_right (hy n)) k
        simpa only [Finset.sum_range_succ, add_sub_cancel_left] using h
      have hmult := mul_le_mul_of_nonneg_left (ih (n+1))
        (mul_nonneg (by positivity : 0 ≤ (k:ℝ)+1) (hy n))
      have hfactorial : (Nat.factorial (k+1) : ℝ) = ((k:ℝ)+1)*(Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      calc
        (∑ t ∈ Finset.range (n+1), y t)^(k+1) ≤
            (∑ t ∈ Finset.range n, y t)^(k+1) +
              (((k:ℝ)+1)*y n) * (∑ t ∈ Finset.range (n+1), y t)^k := hinc
        _ ≤ (Nat.factorial (k+1) : ℝ)*orderedProducts y (k+1) n +
            (((k:ℝ)+1)*y n)*((Nat.factorial k : ℝ)*orderedProducts y k (n+1)) :=
          add_le_add ihn hmult
        _ = (Nat.factorial (k+1) : ℝ)*orderedProducts y (k+1) (n+1) := by
          rw [orderedProducts_step, hfactorial]
          ring

end
end Tournament.OrderedMoments
