module

public import Tournament.Upper.EstimatorBlockMoment
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

theorem referenceEstimate_abs_le (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ)
    (f : ι → ℝ) (L0 : ℝ)
    (hbound : ∀ t s k, |applyEstimator Ψ s (loss t) k| ≤ L0*f s)
    (n : ℕ) (hist : History ι n) (k : ι) :
    |referenceEstimate Ψ loss n hist k| ≤ L0*stateTotal f n hist := by
  calc
    _ ≤ ∑ t ∈ Finset.range (n+1), |applyEstimator Ψ (stateAt n hist t) (loss t) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (n+1), L0*f (stateAt n hist t) :=
      Finset.sum_le_sum (fun t _ ↦ hbound t (stateAt n hist t) k)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem correctedChunkEstimate_abs_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hbound : ∀ t s k, |applyEstimator Ψ s (loss t) k| ≤ L0*f s)
    (n : ℕ) (hist : History ι n) (k : ι) :
    |referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist| ≤
      (4/3)*L0*stateTotal f n hist := by
  have hR := R.likelihood_pos loss hloss M hM n hist
  have hRlow := (R.likelihood_bounds loss hloss M hM n hist).1
  have hraw := referenceEstimate_abs_le Ψ loss f L0 hbound n hist k
  have hV : 0 ≤ stateTotal f n hist := Finset.sum_nonneg (fun t _ ↦ hf0 (stateAt n hist t))
  rw [abs_div, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  nlinarith [mul_nonneg (mul_nonneg hL0 hV) (sub_nonneg.mpr hRlow)]

def blockCorrectedEstimate (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (M : ℝ) :
    (offset : ℕ) → (ns : List ℕ) → BlockOutcome ι ns → ι → ℝ
  | _, [], _, _ => 0
  | offset, n::ns, outcome, k =>
      referenceEstimate Ψ (fun t ↦ loss (offset+t)) n outcome.1 k /
        (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n outcome.1 +
      blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns outcome.2 k

omit [Fintype ι] in
theorem blockRatioTotal_nonneg (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (ns : List ℕ) (outcome : BlockOutcome ι ns) : 0 ≤ blockRatioTotal f ns outcome := by
  induction ns with
  | nil => exact le_rfl
  | cons n ns ih =>
    exact add_nonneg (Finset.sum_nonneg (fun t _ ↦ hf (stateAt n outcome.1 t))) (ih outcome.2)

omit [Fintype ι] in
theorem blockRatioTotal_le (f : ι → ℝ) (b : ℝ) (hf : ∀ i, f i ≤ b)
    (ns : List ℕ) (outcome : BlockOutcome ι ns) :
    blockRatioTotal f ns outcome ≤ (Restarts.totalRounds ns:ℝ)*b := by
  induction ns with
  | nil => simp [blockRatioTotal, Restarts.totalRounds]
  | cons n ns ih =>
    have hhead : stateTotal f n outcome.1 ≤ ((n:ℝ)+1)*b := by
      calc
        _ ≤ ∑ t ∈ Finset.range (n+1), b := Finset.sum_le_sum (fun t _ ↦ hf (stateAt n outcome.1 t))
        _ = _ := by simp
    have htail := ih outcome.2
    change stateTotal f n outcome.1 + blockRatioTotal f ns outcome.2 ≤ _
    calc
      _ ≤ ((n:ℝ)+1)*b+(Restarts.totalRounds ns:ℝ)*b := add_le_add hhead htail
      _ = _ := by simp only [Restarts.totalRounds, Nat.cast_add, Nat.cast_one]; ring

theorem blockCorrectedEstimate_abs_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hbound : ∀ t s k, |applyEstimator Ψ s (loss t) k| ≤ L0*f s) :
    ∀ ns offset (outcome : BlockOutcome ι ns) k,
    |blockCorrectedEstimate R Ψ loss M offset ns outcome k| ≤ (4/3)*L0*blockRatioTotal f ns outcome := by
  intro ns
  induction ns with
  | nil => intro offset outcome k; simp [blockCorrectedEstimate, blockRatioTotal]
  | cons n ns ih =>
    intro offset outcome k
    have hhead := correctedChunkEstimate_abs_le (R.shift offset) Ψ (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM f hf0 L0 hL0 (fun t s k ↦ hbound (offset+t) s k) n outcome.1 k
    have htail := ih (offset+(n+1)) outcome.2 k
    change |referenceEstimate Ψ (fun t ↦ loss (offset+t)) n outcome.1 k /
      (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n outcome.1 +
      blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns outcome.2 k| ≤ _
    calc
      _ ≤ |referenceEstimate Ψ (fun t ↦ loss (offset+t)) n outcome.1 k /
          (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n outcome.1| +
          |blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns outcome.2 k| := abs_add_le _ _
      _ ≤ (4/3)*L0*stateTotal f n outcome.1+(4/3)*L0*blockRatioTotal f ns outcome.2 := add_le_add hhead htail
      _ = _ := by change _ = (4/3)*L0*(stateTotal f n outcome.1+blockRatioTotal f ns outcome.2); ring

theorem blockCorrectedEstimate_norm_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hbound : ∀ t s k, |applyEstimator Ψ s (loss t) k| ≤ L0*f s)
    (ns : List ℕ) (offset : ℕ) (outcome : BlockOutcome ι ns) :
    ‖blockCorrectedEstimate R Ψ loss M offset ns outcome‖ ≤ (4/3)*L0*blockRatioTotal f ns outcome := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL0)
    (blockRatioTotal_nonneg f hf0 ns outcome))).mpr
  intro k
  simpa only [Real.norm_eq_abs] using
    blockCorrectedEstimate_abs_le R Ψ loss hloss M hM f hf0 L0 hL0 hbound ns offset outcome k

end
end Tournament.Upper
