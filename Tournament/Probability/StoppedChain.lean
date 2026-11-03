module

public import Tournament.Probability.ChronologicalPath
public import Tournament.Probability.Restarts
public import Mathlib.Data.Fintype.Option

@[expose] public section

namespace Tournament.StoppedChain

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

def initial (μ : ProbabilityVector ι) : ProbabilityVector (Option ι) where
  weight i := match i with | none => 0 | some j => μ j
  nonneg i := by cases i; exact le_rfl; exact μ.nonneg _
  sum_eq_one := by simpa [Fintype.sum_option] using μ.sum_eq_one

theorem initial_mean (μ : ProbabilityVector ι) (f : Option ι → ℝ) :
    (initial μ).mean f = μ.mean (fun i ↦ f (some i)) := by
  simp [initial, ProbabilityVector.mean, Fintype.sum_option]

def kernel (P : FiniteKernel ι) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) : FiniteKernel (Option ι) where
  entry i j := match i,j with
    | none, none => 1
    | none, some _ => 0
    | some _, none => τ
    | some s, some r => (1-τ)*P s r
  nonneg i j := by
    cases i <;> cases j
    · exact zero_le_one
    · exact le_rfl
    · exact hτ
    · exact mul_nonneg (sub_nonneg.mpr hτ1) (P.nonneg _ _)
  row_sum i := by
    cases i
    · simp [Fintype.sum_option]
    · simp [Fintype.sum_option, ← Finset.mul_sum, P.row_sum]

theorem row_none_mean (P : FiniteKernel ι) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (f : Option ι → ℝ) : ((kernel P τ hτ hτ1).row none).mean f = f none := by
  simp [kernel, FiniteKernel.row, ProbabilityVector.mean, Fintype.sum_option]

theorem row_some_mean (P : FiniteKernel ι) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i : ι) (f : Option ι → ℝ) :
    ((kernel P τ hτ hτ1).row (some i)).mean f =
      τ*f none+(1-τ)*(P.row i).mean (fun j ↦ f (some j)) := by
  simp only [FiniteKernel.row, ProbabilityVector.mean, kernel, Fintype.sum_option]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem law_from_none (P : FiniteKernel ι) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (n : ℕ) (f : History (Option ι) n → ℝ) :
    (law (kernel P τ hτ hτ1) (ProbabilityVector.pure none) n).mean f = f (constantHistory none n) := by
  induction n with
  | zero => exact ProbabilityVector.pure_mean none f
  | succ n ih =>
    change ((law (kernel P τ hτ hτ1) (ProbabilityVector.pure none) n).joint
      (fun hist ↦ (kernel P τ hτ hτ1).row (lastState n hist))).mean f = _
    rw [ProbabilityVector.joint_mean, ih]
    have hlast : lastState n (constantHistory (none : Option ι) n) = none := by cases n <;> rfl
    rw [hlast, row_none_mean]
    rfl

theorem stopped_first_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) (f : History (Option ι) (n+1) → ℝ) :
    (law (kernel P τ hτ hτ1) (initial μ) (n+1)).mean f =
      μ.mean (fun i ↦ τ*f (prepend (some i) n (constantHistory none n)) +
        (1-τ)*(law (kernel P τ hτ hτ1) (initial (P.row i)) n).mean
          (fun hist ↦ f (prepend (some i) n hist))) := by
  rw [law_first_mean, initial_mean]
  congr 1
  funext i
  rw [law_mean_initial_state, row_some_mean, law_from_none]
  have hfuture : (law (kernel P τ hτ hτ1) (initial (P.row i)) n).mean
      (fun hist ↦ f (prepend (some i) n hist)) =
      (P.row i).mean (fun j ↦ (law (kernel P τ hτ hτ1) (ProbabilityVector.pure (some j)) n).mean
        (fun hist ↦ f (prepend (some i) n hist))) := by
    rw [law_mean_initial_state (kernel P τ hτ hτ1) (initial (P.row i)) n, initial_mean]
  rw [hfuture]

def pad : (n m : ℕ) → m ≤ n → History ι m → History (Option ι) n
  | 0, 0, _, i => some i
  | 0, m+1, h, _ => False.elim (Nat.not_succ_le_zero m h)
  | n+1, 0, _, i => prepend (some i) n (constantHistory none n)
  | n+1, m+1, h, hist => prepend (some (firstState (m+1) hist)) n
      (pad n m (by omega) (dropFirst m hist))

omit [Fintype ι] in
theorem pad_prepend (n m : ℕ) (hm : m ≤ n) (i : ι) (hist : History ι m) :
    pad (n+1) (m+1) (by omega) (prepend i m hist) = prepend (some i) n (pad n m hm hist) := by
  change prepend (some (firstState (m+1) (prepend i m hist))) n
    (pad n m _ (dropFirst m (prepend i m hist))) = _
  rw [firstState_prepend, dropFirst_prepend]

end
end Tournament.StoppedChain
