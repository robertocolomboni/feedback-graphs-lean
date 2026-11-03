module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Model

open scoped BigOperators

variable {ι : Type*}

def accumulatedLoss (T : ℕ) (loss : ℕ → ι → ℝ) (path : ℕ → ι) : ℝ :=
  ∑ t ∈ Finset.range T, loss t (path t)

def fixedLoss (T : ℕ) (loss : ℕ → ι → ℝ) (i : ι) : ℝ :=
  ∑ t ∈ Finset.range T, loss t i

def switchCount [DecidableEq ι] (T : ℕ) (path : ℕ → ι) : ℕ :=
  ∑ t ∈ Finset.range (T - 1), if path (t + 1) = path t then 0 else 1

def comparison [DecidableEq ι] (T : ℕ) (loss : ℕ → ι → ℝ)
    (path : ℕ → ι) (i : ι) : ℝ :=
  accumulatedLoss T loss path + switchCount T path - fixedLoss T loss i

def shiftLoss (loss : ℕ → ι → ℝ) (c : ℕ → ℝ) : ℕ → ι → ℝ :=
  fun t i ↦ loss t i - c t

theorem accumulatedLoss_shift (T : ℕ) (loss : ℕ → ι → ℝ)
    (path : ℕ → ι) (c : ℕ → ℝ) :
    accumulatedLoss T (shiftLoss loss c) path =
      accumulatedLoss T loss path - ∑ t ∈ Finset.range T, c t := by
  simp [accumulatedLoss, shiftLoss, Finset.sum_sub_distrib]

theorem fixedLoss_shift (T : ℕ) (loss : ℕ → ι → ℝ)
    (i : ι) (c : ℕ → ℝ) :
    fixedLoss T (shiftLoss loss c) i =
      fixedLoss T loss i - ∑ t ∈ Finset.range T, c t := by
  simp [fixedLoss, shiftLoss, Finset.sum_sub_distrib]

theorem comparison_shift [DecidableEq ι] (T : ℕ) (loss : ℕ → ι → ℝ)
    (path : ℕ → ι) (i : ι) (c : ℕ → ℝ) :
    comparison T (shiftLoss loss c) path i = comparison T loss path i := by
  unfold comparison
  rw [accumulatedLoss_shift, fixedLoss_shift]
  ring

@[simp] theorem switchCount_constant [DecidableEq ι] (T : ℕ) (i : ι) :
    switchCount T (fun _ ↦ i) = 0 := by
  simp [switchCount]

theorem switchCount_le [DecidableEq ι] (T : ℕ) (path : ℕ → ι) :
    switchCount T path ≤ T - 1 := by
  calc
    switchCount T path ≤ ∑ _t ∈ Finset.range (T - 1), 1 := by
      apply Finset.sum_le_sum
      intro t _
      split <;> simp
    _ = T - 1 := by simp

theorem fixedLoss_nonneg (T : ℕ) (loss : ℕ → ι → ℝ) (i : ι)
    (h : ∀ t < T, ∀ j, 0 ≤ loss t j) : 0 ≤ fixedLoss T loss i := by
  exact Finset.sum_nonneg (fun t ht ↦ h t (Finset.mem_range.mp ht) i)

theorem fixedLoss_le_horizon (T : ℕ) (loss : ℕ → ι → ℝ) (i : ι)
    (h : ∀ t < T, ∀ j, loss t j ≤ 1) : fixedLoss T loss i ≤ T := by
  calc
    fixedLoss T loss i ≤ ∑ _t ∈ Finset.range T, (1:ℝ) := by
      exact Finset.sum_le_sum (fun t ht ↦ h t (Finset.mem_range.mp ht) i)
    _ = T := by simp

section BestFixed

variable [Fintype ι] [Nonempty ι]

def bestFixedLoss (T : ℕ) (loss : ℕ → ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fixedLoss T loss)

def pathRegret [DecidableEq ι] (T : ℕ) (loss : ℕ → ι → ℝ) (path : ℕ → ι) : ℝ :=
  accumulatedLoss T loss path + switchCount T path - bestFixedLoss T loss

theorem bestFixedLoss_le (T : ℕ) (loss : ℕ → ι → ℝ) (i : ι) :
    bestFixedLoss T loss ≤ fixedLoss T loss i := by
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_bestFixedLoss (T : ℕ) (loss : ℕ → ι → ℝ) :
    ∃ i, bestFixedLoss T loss = fixedLoss T loss i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fixedLoss T loss)
  exact ⟨i, hi⟩

theorem bestFixedLoss_nonneg (T : ℕ) (loss : ℕ → ι → ℝ)
    (h : ∀ t < T, ∀ j, 0 ≤ loss t j) : 0 ≤ bestFixedLoss T loss := by
  exact Finset.le_inf' _ _ (fun i _ ↦ fixedLoss_nonneg T loss i h)

theorem bestFixedLoss_shift (T : ℕ) (loss : ℕ → ι → ℝ) (c : ℕ → ℝ) :
    bestFixedLoss T (shiftLoss loss c) =
      bestFixedLoss T loss - ∑ t ∈ Finset.range T, c t := by
  obtain ⟨i, hi⟩ := exists_bestFixedLoss T loss
  obtain ⟨j, hj⟩ := exists_bestFixedLoss T (shiftLoss loss c)
  apply le_antisymm
  · calc
      bestFixedLoss T (shiftLoss loss c) ≤ fixedLoss T (shiftLoss loss c) i :=
        bestFixedLoss_le T (shiftLoss loss c) i
      _ = fixedLoss T loss i - ∑ t ∈ Finset.range T, c t := fixedLoss_shift T loss i c
      _ = bestFixedLoss T loss - ∑ t ∈ Finset.range T, c t := by rw [hi]
  · rw [hj, fixedLoss_shift]
    exact sub_le_sub_right (bestFixedLoss_le T loss j) _

theorem pathRegret_shift [DecidableEq ι] (T : ℕ) (loss : ℕ → ι → ℝ)
    (path : ℕ → ι) (c : ℕ → ℝ) :
    pathRegret T (shiftLoss loss c) path = pathRegret T loss path := by
  unfold pathRegret
  rw [accumulatedLoss_shift, bestFixedLoss_shift]
  ring

theorem constant_action_regret_le_horizon [DecidableEq ι] (T : ℕ) (loss : ℕ → ι → ℝ) (i : ι)
    (h0 : ∀ t < T, ∀ j, 0 ≤ loss t j)
    (h1 : ∀ t < T, ∀ j, loss t j ≤ 1) :
    pathRegret T loss (fun _ ↦ i) ≤ T := by
  have hbest := bestFixedLoss_nonneg T loss h0
  have hfixed := fixedLoss_le_horizon T loss i h1
  unfold pathRegret
  rw [switchCount_constant]
  simp only [Nat.cast_zero, add_zero]
  change fixedLoss T loss i - bestFixedLoss T loss ≤ T
  linarith

end BestFixed
end Tournament.Model
