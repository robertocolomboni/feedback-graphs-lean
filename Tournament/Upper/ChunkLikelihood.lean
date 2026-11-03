module

public import Tournament.Upper.Scores
public import Tournament.Probability.FinitePath
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

namespace ScoreRule

variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def stoppedSum (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) :
    (n : ℕ) → History ι n → ℝ
  | 0, _ => 0
  | n+1, (hist,j) => stoppedSum R loss M n hist +
      (if |stoppedSum R loss M n hist| ≤ M-1 then R.score n (loss n) (lastState n hist) j else 0)

def effectiveScore (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) (j : ι) : ℝ :=
  if |R.stoppedSum loss M n hist| ≤ M-1 then R.score n (loss n) (lastState n hist) j else 0

theorem stoppedSum_step (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) (j : ι) :
    R.stoppedSum loss M (n+1) (hist,j) =
      R.stoppedSum loss M n hist + R.effectiveScore loss M n hist j := rfl

theorem effectiveScore_zero_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ)
    (n : ℕ) (hist : History ι n) :
    (P.row (lastState n hist)).mean (R.effectiveScore loss M n hist) = 0 := by
  by_cases h : |R.stoppedSum loss M n hist| ≤ M-1
  · change (∑ j, P (lastState n hist) j * R.effectiveScore loss M n hist j) = 0
    simp only [effectiveScore, ite_eq_left h]
    exact R.zero_mean n (loss n) (hloss n) (lastState n hist)
  · simp [effectiveScore, h, ProbabilityVector.mean]

theorem stoppedSum_abs_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) : |R.stoppedSum loss M n hist| ≤ M := by
  induction n with
  | zero => simp only [stoppedSum, abs_zero]; linarith
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    rw [stoppedSum_step]
    by_cases h : |R.stoppedSum loss M n hist| ≤ M-1
    · rw [effectiveScore, ite_eq_left h]
      have hscore := R.score_abs_le_one n (hloss n) (lastState n hist) j
      exact le_trans (abs_add_le _ _) (by linarith)
    · rw [effectiveScore, ite_eq_right h, add_zero]
      exact ih hist

def steeringStrength (M : ℝ) : ℝ := 1 / (4 * M)

theorem steeringStrength_pos {M : ℝ} (hM : 1 ≤ M) : 0 < steeringStrength M := by
  unfold steeringStrength
  positivity

theorem steeringStrength_mul {M : ℝ} (hM : 1 ≤ M) : steeringStrength M * M = 1/4 := by
  have hM0 : M ≠ 0 := ne_of_gt (by linarith)
  unfold steeringStrength
  field_simp

def likelihood (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) : ℝ :=
  1 + steeringStrength M * R.stoppedSum loss M n hist

theorem likelihood_bounds (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) :
    3/4 ≤ R.likelihood loss M n hist ∧ R.likelihood loss M n hist ≤ 5/4 := by
  have hs := R.stoppedSum_abs_le loss hloss M hM n hist
  have hs' := abs_le.mp hs
  have hβ := steeringStrength_pos hM
  have hprod := steeringStrength_mul hM
  have hlow := mul_le_mul_of_nonneg_left hs'.1 (le_of_lt hβ)
  have hhigh := mul_le_mul_of_nonneg_left hs'.2 (le_of_lt hβ)
  unfold likelihood
  constructor <;> nlinarith

theorem likelihood_pos (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) : 0 < R.likelihood loss M n hist := by
  have h := (R.likelihood_bounds loss hloss M hM n hist).1
  linarith

theorem likelihood_step (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) (j : ι) :
    R.likelihood loss M (n+1) (hist,j) =
      R.likelihood loss M n hist + steeringStrength M * R.effectiveScore loss M n hist j := by
  unfold likelihood
  rw [stoppedSum_step]
  ring

theorem likelihood_next_average (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ)
    (n : ℕ) (hist : History ι n) :
    (P.row (lastState n hist)).mean (fun j ↦ R.likelihood loss M (n+1) (hist,j)) =
      R.likelihood loss M n hist := by
  have heq : (fun j ↦ R.likelihood loss M (n+1) (hist,j)) =
      (fun j ↦ R.likelihood loss M n hist + steeringStrength M * R.effectiveScore loss M n hist j) := by
    funext j
    exact R.likelihood_step loss M n hist j
  rw [heq, ProbabilityVector.mean_add, ProbabilityVector.mean_const,
    ProbabilityVector.mean_const_mul, R.effectiveScore_zero_mean loss hloss M n hist, mul_zero, add_zero]

def tiltedRow (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) : ProbabilityVector ι where
  weight j := P (lastState n hist) j * R.likelihood loss M (n+1) (hist,j) /
    R.likelihood loss M n hist
  nonneg j := div_nonneg
    (mul_nonneg (P.nonneg _ _) (le_of_lt (R.likelihood_pos loss hloss M hM (n+1) (hist,j))))
    (le_of_lt (R.likelihood_pos loss hloss M hM n hist))
  sum_eq_one := by
    rw [← Finset.sum_div]
    change (P.row (lastState n hist)).mean (fun j ↦ R.likelihood loss M (n+1) (hist,j)) /
      R.likelihood loss M n hist = 1
    rw [R.likelihood_next_average loss hloss M n hist]
    exact div_self (ne_of_gt (R.likelihood_pos loss hloss M hM n hist))

def tiltedLaw (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) :
    (n : ℕ) → ProbabilityVector (History ι n)
  | 0 => p
  | n+1 => (tiltedLaw R loss hloss M hM n).joint
      (fun hist ↦ R.tiltedRow loss hloss M hM n hist)

theorem tiltedLaw_likelihood (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) :
    R.tiltedLaw loss hloss M hM n hist = R.likelihood loss M n hist * FinitePath.law P p n hist := by
  induction n with
  | zero => simp [tiltedLaw, likelihood, stoppedSum, FinitePath.law]
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    change R.tiltedLaw loss hloss M hM n hist *
      (P (lastState n hist) j * R.likelihood loss M (n+1) (hist,j) / R.likelihood loss M n hist) =
      R.likelihood loss M (n+1) (hist,j) * (FinitePath.law P p n hist * P (lastState n hist) j)
    rw [ih hist]
    field_simp [ne_of_gt (R.likelihood_pos loss hloss M hM n hist)]

theorem tilted_mean_eq (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (f : History ι n → ℝ) :
    (R.tiltedLaw loss hloss M hM n).mean f =
      (FinitePath.law P p n).mean (fun hist ↦ R.likelihood loss M n hist * f hist) := by
  unfold ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro hist _
  rw [R.tiltedLaw_likelihood loss hloss M hM n hist]
  ring

theorem tilted_nonneg_mean_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (f : History ι n → ℝ) (hf : ∀ hist, 0 ≤ f hist) :
    (R.tiltedLaw loss hloss M hM n).mean f ≤ (5/4) * (FinitePath.law P p n).mean f := by
  rw [R.tilted_mean_eq loss hloss M hM n f, ← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro hist
  exact mul_le_mul_of_nonneg_right (R.likelihood_bounds loss hloss M hM n hist).2 (hf hist)

theorem corrected_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (g : History ι n → ℝ) :
    (R.tiltedLaw loss hloss M hM n).mean (fun hist ↦ g hist / R.likelihood loss M n hist) =
      (FinitePath.law P p n).mean g := by
  rw [R.tilted_mean_eq]
  congr 1
  funext hist
  field_simp [ne_of_gt (R.likelihood_pos loss hloss M hM n hist)]

theorem corrected_square_density (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (f : History ι n → ℝ) :
    (R.tiltedLaw loss hloss M hM n).mean (fun hist ↦ f hist / (R.likelihood loss M n hist)^2) =
      (FinitePath.law P p n).mean (fun hist ↦ f hist / R.likelihood loss M n hist) := by
  rw [R.tilted_mean_eq]
  congr 1
  funext hist
  field_simp [ne_of_gt (R.likelihood_pos loss hloss M hM n hist)]

theorem corrected_square_mean_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (f : History ι n → ℝ) (hf : ∀ hist, 0 ≤ f hist) :
    (R.tiltedLaw loss hloss M hM n).mean (fun hist ↦ f hist / (R.likelihood loss M n hist)^2) ≤
      (4/3) * (FinitePath.law P p n).mean f := by
  rw [R.corrected_square_density, ← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro hist
  have hlo := (R.likelihood_bounds loss hloss M hM n hist).1
  apply (div_le_iff₀ (R.likelihood_pos loss hloss M hM n hist)).mpr
  nlinarith [mul_nonneg (hf hist) (by linarith : 0 ≤ R.likelihood loss M n hist - 3/4)]

theorem corrected_second_moment {κ : Type*} [Fintype κ]
    (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (w : ProbabilityVector κ) (G : History ι n → κ → ℝ) :
    (R.tiltedLaw loss hloss M hM n).mean
        (fun hist ↦ w.squareNorm (fun k ↦ G hist k / R.likelihood loss M n hist)) ≤
      (4/3) * (FinitePath.law P p n).mean (fun hist ↦ w.squareNorm (G hist)) := by
  simp only [ProbabilityVector.squareNorm_div]
  exact R.corrected_square_mean_le loss hloss M hM n
    (fun hist ↦ w.squareNorm (G hist)) (fun hist ↦ w.squareNorm_nonneg (G hist))

end ScoreRule
end
end Tournament.Upper
