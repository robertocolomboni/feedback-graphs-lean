module

public import Tournament.Upper.AdaptivePreparation

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section

set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def bias (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (B b : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ι → ℝ :=
  let π := (A.algorithm n loss hloss).current B b x
  (A.playedRow n loss hloss b π).truncationBias (learningRate (Fintype.card ι) A.T A.m)
    (A.raw n loss b π)

def costs (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (default : ι) (B b : ℕ) (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℝ :=
  if h : b<B then blockCost default loss (prefixHorizon (fun b ↦ n b+1) b)
    (past (b+1) B (by omega) x).2 else 0

def charge (A : SteeringParameters ι) (n : ℕ → ℕ) (b : ℕ) : ℝ :=
  1+6*meanRate A.m*((n b:ℝ)+1)+failure (Fintype.card ι) A.T*((n b:ℝ)+1)^3

theorem smoothed_eq_anchor (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (B b : ℕ) (hb : b≤B)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    smoothedWeights (learningRate (Fintype.card ι) A.T A.m)
      ((A.algorithm n loss hloss).estimates B) (1/(A.T:ℝ)) A.smoothing_nonneg
        (by linarith [A.smoothing_le_half]) b x=
          A.anchor ((A.algorithm n loss hloss).current B b x) := by
  change smooth (weights (A.algorithm n loss hloss).rate
    ((A.algorithm n loss hloss).estimates B) b x) _ _ _=_
  rw [AdaptiveEW.weights_eq_current _ b B hb x]
  rfl

theorem adaptive_estimate_range (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (B b : ℕ) (hb : b<B)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    learningRate (Fintype.card ι) A.T A.m*‖(A.algorithm n loss hloss).estimates B b x‖≤1 := by
  rw [AdaptiveEW.estimates_of_lt _ B b hb x]
  exact truncateEstimate_range _ _

theorem adaptive_bias_bound (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B b : ℕ)
    (hn : n b+1≤horizon A.m)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    ‖A.bias n loss hloss B b x‖≤
      (2:ℝ)^6*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m := by
  exact (A.playedRow_guarantee n loss hloss default b hn
    ((A.algorithm n loss hloss).current B b x)).bias

theorem adaptive_calibration (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B b : ℕ) (hb : b<B)
    (hn : n b+1≤horizon A.m) (i : ι) :
    ((A.algorithm n loss hloss).execution B).toMeasure[
      fun x ↦ (A.algorithm n loss hloss).estimates B b x i |
        AdaptiveEW.histories B b] =ᵐ[((A.algorithm n loss hloss).execution B).toMeasure]
      fun x ↦ (smoothedWeights (learningRate (Fintype.card ι) A.T A.m)
        ((A.algorithm n loss hloss).estimates B) (1/(A.T:ℝ)) A.smoothing_nonneg
          (by linarith [A.smoothing_le_half]) b x).center
            (scheduledBlockLoss (fun b ↦ n b+1) loss b) i-A.bias n loss hloss B b x i := by
  rw [AdaptiveEW.histories_of_le (Y := fun b ↦ DyadicBlockOutcome ι A.m (n b)) B b (by omega)]
  have hce := (A.algorithm n loss hloss).condExp_estimate b B hb i
  filter_upwards [hce] with x hx
  rw [hx,smoothed_eq_anchor A n loss hloss B b (by omega) x]
  dsimp only [bias]
  rw [AdaptiveEW.current_of_le _ B b (by omega) x]
  exact (A.playedRow_guarantee n loss hloss default b hn
    ((A.algorithm n loss hloss).distribution b (past b B (by omega) x))).mean i

theorem adaptive_cost_condition (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B b : ℕ) (hb : b<B)
    (hn : n b+1≤horizon A.m) :
    let P := A.algorithm n loss hloss
    let μ := (P.execution B).toMeasure
    let w := smoothedWeights (learningRate (Fintype.card ι) A.T A.m)
      (P.estimates B) (1/(A.T:ℝ)) A.smoothing_nonneg (by linarith [A.smoothing_le_half])
    μ[A.costs n loss default B b | AdaptiveEW.histories B b] ≤ᵐ[μ] fun x ↦
      (w b x).mean (scheduledBlockLoss (fun b ↦ n b+1) loss b)+A.charge n b-
        2*learningRate (Fintype.card ι) A.T A.m*
          (μ[fun y ↦ (w b y).squareNorm (P.estimates B b y) | AdaptiveEW.histories B b]) x := by
  let P := A.algorithm n loss hloss
  let Y := fun b ↦ DyadicBlockOutcome ι A.m (n b)
  let μ := (P.execution B).toMeasure
  let w := smoothedWeights (learningRate (Fintype.card ι) A.T A.m)
    (P.estimates B) (1/(A.T:ℝ)) A.smoothing_nonneg (by linarith [A.smoothing_le_half])
  let fC := fun s : History Y (b+1) ↦ blockCost default loss (prefixHorizon (fun b ↦ n b+1) b) s.2
  let fQ := fun s : History Y (b+1) ↦ (A.anchor (P.distribution b s.1)).squareNorm
    (P.blockEstimate b s)
  have hCeq : A.costs n loss default B b=(fun x ↦ fC (past (b+1) B (by omega) x)) := by
    funext x
    simp only [costs,dite_eq_left hb]
    rfl
  have hQeq : (fun x ↦ (w b x).squareNorm (P.estimates B b x))=
      (fun x ↦ fQ (past (b+1) B (by omega) x)) := by
    funext x
    have hwx : w b x=A.anchor (P.current B b x) :=
      smoothed_eq_anchor A n loss hloss B b (by omega) x
    rw [hwx,
      AdaptiveEW.current_of_le _ B b (by omega) x,AdaptiveEW.estimates_of_lt P B b hb x]
    change (A.anchor (P.distribution b (past b B (by omega) x))).squareNorm
      (P.blockEstimate b (past (b+1) B (by omega) x))=_
    rw [← AdaptiveEW.past_next_first b B (by omega) x]
  have hCce := condExp_next P.kernel b B (by omega) fC
  have hQce := condExp_next P.kernel b B (by omega) fQ
  change μ[fun x ↦ fC (past (b+1) B (by omega) x) | information b B (by omega)] =ᵐ[μ]
    fun x ↦ (P.kernel b (past b B (by omega) x)).mean (fun y ↦ fC (past b B (by omega) x,y)) at hCce
  change μ[fun x ↦ fQ (past (b+1) B (by omega) x) | information b B (by omega)] =ᵐ[μ]
    fun x ↦ (P.kernel b (past b B (by omega) x)).mean (fun y ↦ fQ (past b B (by omega) x,y)) at hQce
  change μ[A.costs n loss default B b | AdaptiveEW.histories B b] ≤ᵐ[μ] fun x ↦
    (w b x).mean (scheduledBlockLoss (fun b ↦ n b+1) loss b)+A.charge n b-
      2*learningRate (Fintype.card ι) A.T A.m*
        (μ[fun y ↦ (w b y).squareNorm (P.estimates B b y) | AdaptiveEW.histories B b]) x
  rw [hCeq,hQeq,AdaptiveEW.histories_of_le (Y := Y) B b (by omega)]
  filter_upwards [hCce,hQce] with x hxC hxQ
  have hwx : w b x=A.anchor (P.current B b x) :=
    smoothed_eq_anchor A n loss hloss B b (by omega) x
  rw [hxC,hxQ,hwx,
    AdaptiveEW.current_of_le P B b (by omega) x]
  have hc := (A.playedRow_guarantee n loss hloss default b hn
    (P.distribution b (past b B (by omega) x))).cost
  rw [← twice_learningRate] at hc
  dsimp only [fC,fQ,AdaptiveEW.kernel,AdaptiveEW.blockEstimate,P,algorithm,charge]
  dsimp only [P,algorithm] at hc
  linarith

end
end Tournament.Upper.SteeringParameters
