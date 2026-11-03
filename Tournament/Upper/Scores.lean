module

public import Tournament.Probability.FiniteKernel
public import Tournament.Graphs.Feedback
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators
open scoped Classical

variable {ι : Type*} [Fintype ι]

def BoundedLoss (loss : ι → ℝ) : Prop := ∀ i, 0 ≤ loss i ∧ loss i ≤ 1

def ComparisonEquivalent (F : ι → ι → Prop) (s : ι) (f g : ι → ℝ) : Prop :=
  ∀ i j, InClosedNeighborhood F s i → InClosedNeighborhood F s j →
    f i - f j = g i - g j

noncomputable section

def offScore (F : ι → ι → Prop) (loss : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if F i j then loss i - loss j else 0

def compensation (F : ι → ι → Prop) (P : FiniteKernel ι)
    (loss : ι → ℝ) (i : ι) : ℝ := ∑ j, P i j * offScore F loss i j

def tournamentScore (F : ι → ι → Prop) (P : FiniteKernel ι)
    (loss : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if j=i then -(compensation F P loss i) / P i i else offScore F loss i j

def scoreFromComparisons (F : ι → ι → Prop) (P : FiniteKernel ι)
    (i : ι) (delta : ι → ℝ) (j : ι) : ℝ := by
  classical
  exact if j=i then -(∑ k, P i k * (if F i k then delta k else 0)) / P i i
    else if F i j then delta j else 0

omit [Fintype ι] in

theorem observed_comparison_reconstruction (F : ι → ι → Prop) (loss : ι → ℝ)
    (s i j : ι) (hi : InClosedNeighborhood F s i) (hj : InClosedNeighborhood F s j) :
    (if F s j then loss s - loss j else 0) -
      (if F s i then loss s - loss i else 0) = loss i - loss j := by
  have anchor : ∀ k, InClosedNeighborhood F s k →
      (if F s k then loss s - loss k else 0) = loss s - loss k := by
    intro k hk
    rcases hk with hk | hk
    · subst k
      simp
    · simp [hk]
  rw [anchor i hi, anchor j hj]
  ring

theorem score_from_comparisons (F : ι → ι → Prop) (P : FiniteKernel ι)
    (loss : ι → ℝ) (i j : ι) :
    tournamentScore F P loss i j =
      scoreFromComparisons F P i (fun k ↦ loss i - loss k) j := by
  classical
  rfl

theorem decoder_uses_observed_comparisons (F : ι → ι → Prop) (P : FiniteKernel ι)
    (i : ι) (delta delta' : ι → ℝ) (h : ∀ j, F i j → delta j = delta' j) (j : ι) :
    scoreFromComparisons F P i delta j = scoreFromComparisons F P i delta' j := by
  classical
  have hoff : (fun k ↦ if F i k then delta k else (0:ℝ)) =
      (fun k ↦ if F i k then delta' k else (0:ℝ)) := by
    funext k
    by_cases he : F i k
    · simp [he, h k he]
    · simp [he]
  have hoffj : (if F i j then delta j else (0:ℝ)) =
      (if F i j then delta' j else (0:ℝ)) := congrFun hoff j
  have hcomp : (∑ k, P i k * (if F i k then delta k else 0)) =
      (∑ k, P i k * (if F i k then delta' k else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [congrFun hoff k]
  simp only [scoreFromComparisons, hcomp, hoffj]

omit [Fintype ι] in
@[simp] theorem offScore_self (F : ι → ι → Prop) (loss : ι → ℝ) (i : ι) :
    offScore F loss i i = 0 := by
  classical
  simp [offScore]

omit [Fintype ι] in
theorem offScore_comparison_invariant (F : ι → ι → Prop) {f g : ι → ℝ} {i : ι}
    (h : ComparisonEquivalent F i f g) (j : ι) : offScore F f i j = offScore F g i j := by
  classical
  by_cases he : F i j
  · simp only [offScore, ite_eq_left he]
    exact h i j (Or.inl rfl) (Or.inr he)
  · simp [offScore, he]

theorem score_comparison_invariant (F : ι → ι → Prop) (P : FiniteKernel ι)
    {f g : ι → ℝ} {i : ι} (h : ComparisonEquivalent F i f g) (j : ι) :
    tournamentScore F P f i j = tournamentScore F P g i j := by
  classical
  have hoff : offScore F f i = offScore F g i := by
    funext k
    exact offScore_comparison_invariant F h k
  simp only [tournamentScore, compensation, hoff]

theorem score_weighted_entry (F : ι → ι → Prop) (P : FiniteKernel ι)
    (loss : ι → ℝ) (i j : ι) (hpii : 0 < P i i) :
    P i j * tournamentScore F P loss i j =
      P i j * offScore F loss i j - (if j=i then compensation F P loss i else 0) := by
  classical
  by_cases hij : j=i
  · subst j
    simp only [tournamentScore, ite_true, offScore_self, mul_zero, zero_sub]
    field_simp [ne_of_gt hpii]
  · simp [tournamentScore, hij]

theorem score_zero_mean (F : ι → ι → Prop) (P : FiniteKernel ι)
    (loss : ι → ℝ) (i : ι) (hpii : 0 < P i i) :
    ∑ j, P i j * tournamentScore F P loss i j = 0 := by
  classical
  simp_rw [score_weighted_entry F P loss i _ hpii]
  rw [Finset.sum_sub_distrib]
  simp [compensation]

omit [Fintype ι] in
theorem offScore_abs_le_one (F : ι → ι → Prop) {loss : ι → ℝ}
    (hloss : BoundedLoss loss) (i j : ι) : |offScore F loss i j| ≤ 1 := by
  classical
  by_cases he : F i j
  · simp only [offScore, ite_eq_left he, abs_le]
    constructor <;> linarith [(hloss i).1, (hloss i).2, (hloss j).1, (hloss j).2]
  · simp [offScore, he]

theorem off_diagonal_score_abs (F : ι → ι → Prop) (P : FiniteKernel ι)
    {loss : ι → ℝ} (hloss : BoundedLoss loss) {i j : ι} (hij : j ≠ i) :
    |tournamentScore F P loss i j| ≤ 1 := by
  classical
  simpa only [tournamentScore, ite_eq_right hij] using offScore_abs_le_one F hloss i j

theorem compensation_abs_le (F : ι → ι → Prop) (P : FiniteKernel ι)
    {loss : ι → ℝ} (hloss : BoundedLoss loss) (i : ι) :
    |compensation F P loss i| ≤ 1 - P i i := by
  classical
  calc
    |compensation F P loss i| ≤ ∑ j, |P i j * offScore F loss i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P i j * (if j=i then 0 else 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : j=i
      · subst j
        simp
      · rw [ite_eq_right hij, mul_one, abs_mul, abs_of_nonneg (P.nonneg i j)]
        exact mul_le_of_le_one_right (P.nonneg i j) (offScore_abs_le_one F hloss i j)
    _ = 1 - P i i := P.row_switch_probability i

theorem diagonal_score_abs (F : ι → ι → Prop) (P : FiniteKernel ι)
    {loss : ι → ℝ} (hloss : BoundedLoss loss) (i : ι) (hhold : 1/2 ≤ P i i) :
    |tournamentScore F P loss i i| ≤ 2 * (1 - P i i) := by
  classical
  have hp : 0 < P i i := by linarith
  have hs := compensation_abs_le F P hloss i
  have hnonneg : 0 ≤ 1 - P i i := le_trans (abs_nonneg _) hs
  simp only [tournamentScore, ite_true, abs_div, abs_neg, abs_of_pos hp]
  calc
    |compensation F P loss i| / P i i ≤ (1 - P i i) / P i i :=
      (div_le_div_iff_of_pos_right hp).mpr hs
    _ ≤ 2 * (1 - P i i) := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hhold)]

theorem tournament_oriented_sum (F : ι → ι → Prop) (hF : IsTournament F)
    (a : ι → ι → ℝ) (hsym : ∀ i j, a i j = a j i) (hdiag : ∀ i, a i i = 0) :
    (∑ i, ∑ j, a i j) = 2 * ∑ i, ∑ j, if F i j then a i j else 0 := by
  classical
  have hentry : ∀ i j, a i j =
      (if F i j then a i j else 0) + (if F j i then a j i else 0) := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp [hdiag]
    · by_cases he : F i j
      · have hn : ¬ F j i := fun hj ↦ (hF i j hij).2 ⟨he,hj⟩
        simp [he, hn]
      · have he' : F j i := (hF i j hij).1.resolve_left he
        simp [he, he', hsym]
  calc
    (∑ i, ∑ j, a i j) =
        ∑ i, ∑ j, ((if F i j then a i j else 0) +
          (if F j i then a j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hentry i j
    _ =
        (∑ i, ∑ j, if F i j then a i j else 0) +
          (∑ i, ∑ j, if F j i then a j i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, if F i j then a i j else 0 := by
      rw [Finset.sum_comm (f := fun i j ↦ if F j i then a j i else 0)]
      ring

theorem score_center_target (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (d : ι → ι → ℝ) (hzero : ∀ i, ∑ j, P i j * d i j = 0) (g : ι → ℝ) :
    P.edgeSum p (fun i j ↦ d i j * g j) =
      P.edgeSum p (fun i j ↦ d i j * (g j - g i)) := by
  have hsource : P.edgeSum p (fun i j ↦ d i j * g i) = 0 := by
    unfold FiniteKernel.edgeSum
    apply Finset.sum_eq_zero
    intro i _
    calc
      (∑ j, (p i * P i j) * (d i j * g i)) =
          (p i * g i) * (∑ j, P i j * d i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hzero i, mul_zero]
  have hfun : (fun i j ↦ d i j * (g j - g i)) =
      (fun i j ↦ d i j * g j - d i j * g i) := by
    funext i j
    ring
  rw [hfun, P.edgeSum_sub p, hsource, sub_zero]

theorem tournament_score_dirichlet (F : ι → ι → Prop) (hF : IsTournament F)
    (P : FiniteKernel ι) (p : ProbabilityVector ι) (hrev : P.Reversible p)
    (hhold : ∀ i, 1/2 ≤ P i i) (loss g : ι → ℝ) :
    P.edgeSum p (fun i j ↦ tournamentScore F P loss i j * g j) =
      - FiniteKernel.weightedInner p loss (fun i ↦ g i - P.act g i) := by
  classical
  let a : ι → ι → ℝ := fun i j ↦ (p i * P i j) * (loss i - loss j) * (g i - g j)
  have hsym : ∀ i j, a i j = a j i := by
    intro i j
    dsimp [a]
    rw [hrev i j]
    ring
  have hdiag : ∀ i, a i i = 0 := by intro i; simp [a]
  have hpair := tournament_oriented_sum F hF a hsym hdiag
  have hzero : ∀ i, ∑ j, P i j * tournamentScore F P loss i j = 0 := by
    intro i
    exact score_zero_mean F P loss i (by linarith [hhold i])
  rw [score_center_target P p _ hzero g]
  have heq : P.edgeSum p (fun i j ↦ tournamentScore F P loss i j * (g j - g i)) =
      -(∑ i, ∑ j, if F i j then a i j else 0) := by
    unfold FiniteKernel.edgeSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : j=i
    · subst j
      simp [a]
    · simp only [tournamentScore, ite_eq_right hij, offScore]
      by_cases he : F i j
      · simp only [ite_eq_left he]
        dsimp [a]
        ring
      · simp [he]
  rw [heq, P.dirichlet_identity p hrev loss g]
  have heq' : P.edgeSum p (fun i j ↦ (loss i - loss j) * (g i - g j)) =
      ∑ i, ∑ j, a i j := by
    unfold FiniteKernel.edgeSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    ring
  rw [heq', hpair]
  ring

structure ScoreRule (F : ι → ι → Prop) (P : FiniteKernel ι) (p : ProbabilityVector ι) where
  sampling_pos : ∀ i, 0 < p i
  reversible : P.Reversible p
  holding : ∀ i, 1/2 ≤ P i i
  score : ℕ → (ι → ℝ) → ι → ι → ℝ
  decoder : ℕ → ι → (ι → ℝ) → ι → ℝ
  decoder_local : ∀ t i delta delta', (∀ j, F i j → delta j = delta' j) →
    ∀ j, decoder t i delta j = decoder t i delta' j
  decoder_eq : ∀ t loss, BoundedLoss loss → ∀ i j,
    score t loss i j = decoder t i (fun k ↦ loss i - loss k) j
  zero_mean : ∀ t loss, BoundedLoss loss → ∀ i, ∑ j, P i j * score t loss i j = 0
  off_diagonal_abs : ∀ t loss, BoundedLoss loss → ∀ i j, j ≠ i → |score t loss i j| ≤ 1
  diagonal_abs : ∀ t loss, BoundedLoss loss → ∀ i, |score t loss i i| ≤ 2 * (1 - P i i)
  correlation : ∀ t loss, BoundedLoss loss → ∀ g, P.edgeSum p (fun i j ↦ score t loss i j * g j) =
    -FiniteKernel.weightedInner p loss (fun i ↦ g i - P.act g i)

def tournamentScoreRule (F : ι → ι → Prop) (hF : IsTournament F)
    (P : FiniteKernel ι) (p : ProbabilityVector ι) (hp : ∀ i, 0 < p i)
    (hrev : P.Reversible p) (hhold : ∀ i, 1/2 ≤ P i i) : ScoreRule F P p where
  sampling_pos := hp
  reversible := hrev
  holding := hhold
  score _ := tournamentScore F P
  decoder _ := scoreFromComparisons F P
  decoder_local _ i delta delta' h j := decoder_uses_observed_comparisons F P i delta delta' h j
  decoder_eq _ loss _hloss i j := score_from_comparisons F P loss i j
  zero_mean _ loss _hloss i := score_zero_mean F P loss i (by linarith [hhold i])
  off_diagonal_abs _ _ hloss _ _ hij := off_diagonal_score_abs F P hloss hij
  diagonal_abs _ _ hloss i := diagonal_score_abs F P hloss i (hhold i)
  correlation _ loss _hloss g := tournament_score_dirichlet F hF P p hrev hhold loss g

theorem tournament_scores_form_scoreRule (F : ι → ι → Prop) (hF : IsTournament F)
    (P : FiniteKernel ι) (p : ProbabilityVector ι) (hp : ∀ i, 0 < p i)
    (hrev : P.Reversible p) (hhold : ∀ i, 1/2 ≤ P i i) :
    ∃ R : ScoreRule F P p, ∀ t loss i j, R.score t loss i j = tournamentScore F P loss i j := by
  exact ⟨tournamentScoreRule F hF P p hp hrev hhold, fun _ _ _ _ ↦ rfl⟩

namespace ScoreRule

theorem decoder_realization {F : ι → ι → Prop} {P : FiniteKernel ι}
    {p : ProbabilityVector ι} (R : ScoreRule F P p) :
    ∃ decode : ℕ → ι → (ι → ℝ) → ι → ℝ,
      ∀ t loss, BoundedLoss loss → ∀ i j,
        R.score t loss i j =
          decode t i (fun k ↦ if F i k then loss i-loss k else 0) j := by
  refine ⟨R.decoder, ?_⟩
  intro t loss hloss i j
  rw [R.decoder_eq t loss hloss i j]
  apply R.decoder_local
  intro k hk
  simp only [ite_eq_left hk]

theorem comparison_invariant {F : ι → ι → Prop} {P : FiniteKernel ι}
    {p : ProbabilityVector ι} (R : ScoreRule F P p) (t : ℕ) {loss loss' : ι → ℝ} {i : ι}
    (hloss : BoundedLoss loss) (hloss' : BoundedLoss loss')
    (h : ComparisonEquivalent F i loss loss') (j : ι) :
    R.score t loss i j = R.score t loss' i j := by
  rw [R.decoder_eq t loss hloss i j, R.decoder_eq t loss' hloss' i j]
  apply R.decoder_local
  intro k he
  exact h i k (Or.inl rfl) (Or.inr he)

theorem score_abs_le_one {F : ι → ι → Prop} {P : FiniteKernel ι}
    {p : ProbabilityVector ι} (R : ScoreRule F P p) (t : ℕ) {loss : ι → ℝ}
    (hloss : BoundedLoss loss) (i j : ι) : |R.score t loss i j| ≤ 1 := by
  classical
  by_cases hij : j=i
  · subst j
    have hd := R.diagonal_abs t loss hloss i
    have hh := R.holding i
    linarith
  · exact R.off_diagonal_abs t loss hloss i j hij

end ScoreRule

end
end Tournament.Upper
