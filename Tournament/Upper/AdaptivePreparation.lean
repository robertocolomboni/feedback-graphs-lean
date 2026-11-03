module

public import Tournament.Model.AdaptiveEW
public import Tournament.Model.BlockAccounting
public import Tournament.Upper.PreparedBlockPolicy
public import Tournament.Upper.RoundedPreparation

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

structure SteeringParameters (ι : Type*) [Fintype ι] where
  tournament : ι → ι → Prop
  isTournament : IsTournament tournament
  T : ℕ
  m : ℕ
  card_ge_two : 2≤Fintype.card ι
  time_ge_two : 2≤T
  bands_ge_five : 5≤m
  rounded : Bool := false

namespace SteeringParameters

structure Preparation (F : ι → ι → Prop) (w : ProbabilityVector ι) (T m : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T) where
  holding : HoldingFamily ι
  rules : DyadicScoreRules holding F m
  estimator : ι → ι → ι → ℝ
  observable : ScoreRule.EstimatorObservable F estimator
  guarantee : ∀ (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (offset n : ℕ)
    (_hn : n+1≤horizon m),
    OneBlockGuarantee (dyadicBlockLaw holding m rules loss hloss (threshold (Fintype.card ι) T)
      (threshold_ge_one hK hT) offset n) w (blockLoss (fun t ↦ loss (offset+t)) (n+1))
      (dyadicBlockCorrectedEstimate holding m rules estimator loss (threshold (Fintype.card ι) T) offset n)
      (blockCost default loss offset) (blockInternalSwitches default) T m n

omit [Nonempty ι] in
theorem smoothing_nonneg (A : SteeringParameters ι) : 0≤1/(A.T:ℝ) := by positivity

omit [Nonempty ι] in
theorem smoothing_le_half (A : SteeringParameters ι) : 1/(A.T:ℝ)≤1/2 := by
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast A.time_ge_two)

def anchor (A : SteeringParameters ι) (π : ProbabilityVector ι) : ProbabilityVector ι :=
  smooth π (1/(A.T:ℝ)) A.smoothing_nonneg (by linarith [A.smoothing_le_half])

theorem anchor_floor (A : SteeringParameters ι) (π : ProbabilityVector ι) (i : ι) :
    1/((Fintype.card ι:ℝ)*(A.T:ℝ))≤A.anchor π i := by
  have hleft := mul_nonneg (show (0:ℝ)≤1-1/(A.T:ℝ) by linarith [A.smoothing_le_half])
    (π.nonneg i)
  have heq : (1/(A.T:ℝ))*(1/(Fintype.card ι:ℝ))=1/((Fintype.card ι:ℝ)*(A.T:ℝ)) := by
    simp only [one_div,mul_inv_rev]
  change 1/((Fintype.card ι:ℝ)*(A.T:ℝ))≤
    (1-1/(A.T:ℝ))*π i+(1/(A.T:ℝ))*(1/(Fintype.card ι:ℝ))
  rw [heq]
  linarith

theorem anchor_pos (A : SteeringParameters ι) (π : ProbabilityVector ι) (i : ι) :
    0<A.anchor π i := by
  have hp : (0:ℝ)<(Fintype.card ι:ℝ)*(A.T:ℝ) :=
    lt_of_lt_of_le (by norm_num) (product_ge_four A.card_ge_two A.time_ge_two)
  exact lt_of_lt_of_le (one_div_pos.mpr hp) (A.anchor_floor π i)

def preparation (A : SteeringParameters ι) (π : ProbabilityVector ι) :
    Preparation A.tournament (A.anchor π) A.T A.m A.card_ge_two A.time_ge_two :=
  if A.rounded then
    { holding := roundedHolding A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.T A.card_ge_two
        A.time_ge_two (A.anchor_floor π) A.m A.bands_ge_five
      rules := roundedRules A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.T A.card_ge_two
        A.time_ge_two (A.anchor_floor π) A.m A.bands_ge_five
      estimator := roundedEstimator A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.T A.card_ge_two
        A.time_ge_two (A.anchor_floor π) A.m A.bands_ge_five
      observable := (rounded_inputs A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.T A.card_ge_two
        A.time_ge_two (A.anchor_floor π) A.m A.bands_ge_five).2.2.2.2.2.observable
      guarantee := rounded_block_guarantee A.tournament A.isTournament (A.anchor π) (A.anchor_pos π)
        A.T A.card_ge_two A.time_ge_two (A.anchor_floor π) A.m A.bands_ge_five }
  else
    { holding := preparedHolding A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.m A.bands_ge_five
      rules := preparedRules A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.m A.bands_ge_five
      estimator := preparedEstimator A.tournament A.isTournament (A.anchor π) (A.anchor_pos π) A.m A.bands_ge_five
      observable := (prepared_inputs A.tournament A.isTournament (A.anchor π) (A.anchor_pos π)
        A.m A.bands_ge_five).2.2.2.2.observable
      guarantee := prepared_block_guarantee A.tournament A.isTournament (A.anchor π) (A.anchor_pos π)
        A.T A.m A.card_ge_two A.time_ge_two A.bands_ge_five (A.anchor_floor π) }

def holding (A : SteeringParameters ι) (π : ProbabilityVector ι) : HoldingFamily ι :=
  (A.preparation π).holding

def rules (A : SteeringParameters ι) (π : ProbabilityVector ι) :
    DyadicScoreRules (A.holding π) A.tournament A.m :=
  (A.preparation π).rules

def estimator (A : SteeringParameters ι) (π : ProbabilityVector ι) : ι → ι → ι → ℝ :=
  (A.preparation π).estimator

def raw (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (b : ℕ)
    (π : ProbabilityVector ι) : DyadicBlockOutcome ι A.m (n b) → ι → ℝ :=
  dyadicBlockCorrectedEstimate (A.holding π) A.m (A.rules π) (A.estimator π) loss
    (threshold (Fintype.card ι) A.T) (prefixHorizon (fun b ↦ n b+1) b) (n b)

def playedRow (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (b : ℕ) (π : ProbabilityVector ι) :
    ProbabilityVector (DyadicBlockOutcome ι A.m (n b)) :=
  dyadicBlockLaw (A.holding π) A.m (A.rules π) loss hloss (threshold (Fintype.card ι) A.T)
    (threshold_ge_one A.card_ge_two A.time_ge_two) (prefixHorizon (fun b ↦ n b+1) b) (n b)

def algorithm (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) :
    AdaptiveEW (fun b ↦ DyadicBlockOutcome ι A.m (n b)) ι where
  rate := learningRate (Fintype.card ι) A.T A.m
  output b π y := truncateEstimate (learningRate (Fintype.card ι) A.T A.m) (A.raw n loss b π y)
  row := A.playedRow n loss hloss

theorem playedRow_guarantee (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (b : ℕ)
    (hn : n b+1≤horizon A.m) (π : ProbabilityVector ι) :
    OneBlockGuarantee (A.playedRow n loss hloss b π) (A.anchor π)
      (scheduledBlockLoss (fun b ↦ n b+1) loss b) (A.raw n loss b π)
      (blockCost default loss (prefixHorizon (fun b ↦ n b+1) b))
      (blockInternalSwitches default) A.T A.m (n b) := by
  exact (A.preparation π).guarantee loss hloss default (prefixHorizon (fun b ↦ n b+1) b) (n b) hn

end SteeringParameters
end
end Tournament.Upper
