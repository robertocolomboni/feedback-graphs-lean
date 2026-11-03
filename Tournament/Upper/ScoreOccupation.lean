module

public import Tournament.Upper.ChunkResponse
public import Tournament.Upper.OccupationPotentials
public import Tournament.Probability.Restarts

@[expose] public section

namespace Tournament.Upper.ScoreRule

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

theorem row_abs_score_le_two_switches (R : ScoreRule F P p) (t : ℕ) (loss : ι → ℝ)
    (hloss : BoundedLoss loss) (i : ι) :
    (P.row i).mean (fun j ↦ |R.score t loss i j|) ≤ 2*(1-P i i) := by
  let d := R.score t loss i
  have hzero : (∑ j ∈ Finset.univ.erase i, P i j*d j) + P i i*d i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact R.zero_mean t loss hloss i
  have hdiag : P i i*|d i| ≤ ∑ j ∈ Finset.univ.erase i, P i j*|d j| := by
    calc
      P i i*|d i| = |P i i*d i| := by rw [abs_mul, abs_of_nonneg (P.nonneg i i)]
      _ = |-(∑ j ∈ Finset.univ.erase i, P i j*d j)| := by
        congr 1
        linarith
      _ = |∑ j ∈ Finset.univ.erase i, P i j*d j| := abs_neg _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |P i j*d j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.univ.erase i, P i j*|d j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (P.nonneg i j)]
  have hoff : (∑ j ∈ Finset.univ.erase i, P i j*|d j|) ≤ 1-P i i := by
    calc
      (∑ j ∈ Finset.univ.erase i, P i j*|d j|) ≤ ∑ j ∈ Finset.univ.erase i, P i j := by
        apply Finset.sum_le_sum
        intro j hj
        have habs := R.off_diagonal_abs t loss hloss i j (Finset.mem_erase.mp hj).1
        exact mul_le_of_le_one_right (P.nonneg i j) habs
      _ = 1-P i i := by
        have hsum := Finset.sum_erase_add Finset.univ (fun j ↦ P i j) (Finset.mem_univ i)
        rw [P.row_sum] at hsum
        linarith
  change (∑ j, P i j*|d j|) ≤ _
  rw [← Finset.sum_erase_add Finset.univ (fun j ↦ P i j*|d j|) (Finset.mem_univ i)]
  linarith

def absoluteScores (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → History ι n → ℝ
  | 0, _ => 0
  | n+1, (hist,j) => absoluteScores R loss n hist + |R.score n (loss n) (lastState n hist) j|

theorem abs_stoppedSum_le_absoluteScores (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) :
    |R.stoppedSum loss M n hist| ≤ R.absoluteScores loss n hist := by
  induction n with
  | zero => simp [stoppedSum, absoluteScores]
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    rw [stoppedSum_step, absoluteScores]
    by_cases h : |R.stoppedSum loss M n hist| ≤ M-1
    · rw [effectiveScore, ite_eq_left h]
      exact le_trans (abs_add_le _ _) (add_le_add (ih hist) le_rfl)
    · rw [effectiveScore, ite_eq_right h, add_zero]
      exact le_trans (ih hist) (le_add_of_nonneg_right (abs_nonneg _))

theorem stop_implies_absoluteScores_gt (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (n : ℕ) (hist : History ι n)
    (hstop : R.stopEvent loss M n hist) : M-1 < R.absoluteScores loss n hist :=
  lt_of_lt_of_le ((R.stopEvent_iff_final_exceeded loss M hM n hist).mp hstop)
    (R.abs_stoppedSum_le_absoluteScores loss M n hist)

theorem absoluteScores_eq_sum (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n) :
    R.absoluteScores loss n hist =
      ∑ t ∈ Finset.range n, |transitionValue (R.score t (loss t)) n hist t| := by
  induction n with
  | zero => simp [absoluteScores]
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    change R.absoluteScores loss n hist + |R.score n (loss n) (lastState n hist) j| = _
    rw [Finset.sum_range_succ]
    have hprefix : (∑ t ∈ Finset.range n, |transitionValue (R.score t (loss t)) (n+1) (hist,j) t|) =
        ∑ t ∈ Finset.range n, |transitionValue (R.score t (loss t)) n hist t| := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [transitionValue_prefix _ n (hist,j) t (Finset.mem_range.mp ht)]
    rw [hprefix, transitionValue_last, ih hist]

theorem absoluteScores_mean_step (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (μ : ProbabilityVector ι) (n : ℕ) :
    (law P μ (n+1)).mean (R.absoluteScores loss (n+1)) =
      (law P μ n).mean (R.absoluteScores loss n) +
        (law P μ n).mean (fun hist ↦ (P.row (lastState n hist)).mean
          (fun j ↦ |R.score n (loss n) (lastState n hist) j|)) := by
  change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
    (fun hist : History ι n × ι ↦ R.absoluteScores loss n hist.1 +
      |R.score n (loss n) (lastState n hist.1) hist.2|) = _
  rw [ProbabilityVector.joint_mean]
  simp only [ProbabilityVector.mean_add, ProbabilityVector.mean_const]

theorem absoluteScores_mean_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (μ : ProbabilityVector ι) (a : ι → ℝ)
    (hrow : ∀ t i, (P.row i).mean (fun j ↦ |R.score t (loss t) i j|) ≤ 2*a i) (n : ℕ) :
    (law P μ n).mean (R.absoluteScores loss n) ≤ 2*(law P μ n).mean (occupation a n) := by
  induction n with
  | zero =>
    have hocc : occupation a 0 = (fun _ : History ι 0 ↦ (0:ℝ)) := by
      funext hist
      simp [occupation]
    have habs : R.absoluteScores loss 0 = (fun _ : History ι 0 ↦ (0:ℝ)) := rfl
    rw [hocc, habs, ProbabilityVector.mean_const]
    norm_num
  | succ n ih =>
    rw [R.absoluteScores_mean_step, occupation_mean_step]
    have hmean : (law P μ n).mean (fun hist ↦ (P.row (lastState n hist)).mean
        (fun j ↦ |R.score n (loss n) (lastState n hist) j|)) ≤
        2*(law P μ n).mean (fun hist ↦ a (lastState n hist)) := by
      rw [← ProbabilityVector.mean_const_mul]
      exact (law P μ n).mean_mono (fun hist ↦ hrow n (lastState n hist))
    linarith

theorem reference_chunk_absoluteScores_le (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (μ : ProbabilityVector ι) (n : ℕ) :
    (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).mean
      (fun outcome ↦ R.absoluteScores loss (Restarts.length n outcome.1) outcome.2) ≤ 7 := by
  have hrow : ∀ t i, ((H.kernel τ hτ).row i).mean (fun j ↦ |R.score t (loss t) i j|) ≤
      2*H.refreshRate τ i := by
    intro t i
    have hscore := R.row_abs_score_le_two_switches t (loss t) (hloss t) i
    have hhold := H.kernel_holding_lower hτ i
    linarith
  have hlength := Restarts.expected_length_le hτ hτ1 n
  have hlength0 : 0 ≤ (Restarts.law τ (le_of_lt hτ) hτ1 n).mean
      (fun coins ↦ (Restarts.length n coins : ℝ)) :=
    ProbabilityVector.mean_nonneg _ (fun coins ↦ Nat.cast_nonneg _)
  have hbar := H.meanRefreshRate_le (le_of_lt hτ)
  have hprod : H.meanRefreshRate τ * (Restarts.law τ (le_of_lt hτ) hτ1 n).mean
      (fun coins ↦ (Restarts.length n coins : ℝ)) ≤ 1/2 := by
    calc
      _ ≤ (τ/2)*(1/τ) := mul_le_mul hbar hlength hlength0 (by positivity)
      _ = 1/2 := by field_simp
  rw [Restarts.referenceChunk_mean]
  calc
    (Restarts.law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦
        (law (H.kernel τ hτ) μ (Restarts.length n coins)).mean
          (fun hist ↦ R.absoluteScores loss (Restarts.length n coins) hist)) ≤
        (Restarts.law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦
          2*((Restarts.length n coins : ℝ)*H.meanRefreshRate τ+3)) := by
      apply ProbabilityVector.mean_mono
      intro coins
      have habs := R.absoluteScores_mean_le loss μ (H.refreshRate τ) hrow (Restarts.length n coins)
      have hocc := H.expected_refresh_occupation_le μ hτ hτ1 (Restarts.length n coins)
      linarith
    _ = 2*(H.meanRefreshRate τ * (Restarts.law τ (le_of_lt hτ) hτ1 n).mean
          (fun coins ↦ (Restarts.length n coins : ℝ))+3) := by
      rw [ProbabilityVector.mean_const_mul, ProbabilityVector.mean_add,
        ProbabilityVector.mean_mul_const, ProbabilityVector.mean_const]
      ring
    _ ≤ 7 := by linarith

end
end Tournament.Upper.ScoreRule
