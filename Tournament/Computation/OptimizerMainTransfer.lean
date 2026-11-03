module

public import Tournament.Computation.OptimizerTransfer
public import Tournament.Upper.TunedExecution

@[expose] public section

namespace Tournament.Computation.OptimizerMainTransfer

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model Upper ExponentialWeights BlockParameters Tuning

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

structure Parameters (ι : Type*) [Fintype ι] [Nonempty ι] extends SteeringParameters ι where
  preparation : (π : ProbabilityVector ι) →
    SteeringParameters.Preparation tournament (toSteeringParameters.anchor π) T m card_ge_two time_ge_two

namespace Parameters

def anchor (A : Parameters ι) (π : ProbabilityVector ι) : ProbabilityVector ι :=
  A.toSteeringParameters.anchor π

theorem smoothing_nonneg (A : Parameters ι) : 0≤1/(A.T:ℝ) :=
  A.toSteeringParameters.smoothing_nonneg

theorem smoothing_le_half (A : Parameters ι) : 1/(A.T:ℝ)≤1/2 :=
  A.toSteeringParameters.smoothing_le_half

def holding (A : Parameters ι) (π : ProbabilityVector ι) : HoldingFamily ι :=
  (A.preparation π).holding

def rules (A : Parameters ι) (π : ProbabilityVector ι) :
    DyadicScoreRules (A.holding π) A.tournament A.m :=
  (A.preparation π).rules

def estimator (A : Parameters ι) (π : ProbabilityVector ι) : ι → ι → ι → ℝ :=
  (A.preparation π).estimator

def raw (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (b : ℕ)
    (π : ProbabilityVector ι) : DyadicBlockOutcome ι A.m (n b) → ι → ℝ :=
  dyadicBlockCorrectedEstimate (A.holding π) A.m (A.rules π) (A.estimator π) loss
    (threshold (Fintype.card ι) A.T) (prefixHorizon (fun b ↦ n b+1) b) (n b)

def playedRow (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (b : ℕ) (π : ProbabilityVector ι) :
    ProbabilityVector (DyadicBlockOutcome ι A.m (n b)) :=
  dyadicBlockLaw (A.holding π) A.m (A.rules π) loss hloss (threshold (Fintype.card ι) A.T)
    (threshold_ge_one A.card_ge_two A.time_ge_two) (prefixHorizon (fun b ↦ n b+1) b) (n b)

def algorithm (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) :
    AdaptiveEW (fun b ↦ DyadicBlockOutcome ι A.m (n b)) ι where
  rate := learningRate (Fintype.card ι) A.T A.m
  output b π y := truncateEstimate (learningRate (Fintype.card ι) A.T A.m) (A.raw n loss b π y)
  row := A.playedRow n loss hloss

theorem playedRow_guarantee (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (b : ℕ)
    (hn : n b+1≤horizon A.m) (π : ProbabilityVector ι) :
    OneBlockGuarantee (A.playedRow n loss hloss b π) (A.anchor π)
      (scheduledBlockLoss (fun b ↦ n b+1) loss b) (A.raw n loss b π)
      (blockCost default loss (prefixHorizon (fun b ↦ n b+1) b))
      (blockInternalSwitches default) A.T A.m (n b) := by
  exact (A.preparation π).guarantee loss hloss default (prefixHorizon (fun b ↦ n b+1) b) (n b) hn

def bias (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (B b : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ι → ℝ :=
  let π := (A.algorithm n loss hloss).current B b x
  (A.playedRow n loss hloss b π).truncationBias (learningRate (Fintype.card ι) A.T A.m)
    (A.raw n loss b π)

def costs (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (default : ι) (B b : ℕ) (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℝ :=
  if h : b<B then blockCost default loss (prefixHorizon (fun b ↦ n b+1) b)
    (past (b+1) B (by omega) x).2 else 0

def charge (A : Parameters ι) (n : ℕ → ℕ) (b : ℕ) : ℝ :=
  1+6*meanRate A.m*((n b:ℝ)+1)+failure (Fintype.card ι) A.T*((n b:ℝ)+1)^3

theorem smoothed_eq_anchor (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
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

theorem adaptive_estimate_range (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (B b : ℕ) (hb : b<B)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    learningRate (Fintype.card ι) A.T A.m*‖(A.algorithm n loss hloss).estimates B b x‖≤1 := by
  rw [AdaptiveEW.estimates_of_lt _ B b hb x]
  exact truncateEstimate_range _ _

theorem adaptive_bias_bound (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B b : ℕ)
    (hn : n b+1≤horizon A.m)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    ‖A.bias n loss hloss B b x‖≤
      (2:ℝ)^6*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m := by
  exact (A.playedRow_guarantee n loss hloss default b hn
    ((A.algorithm n loss hloss).current B b x)).bias

theorem adaptive_calibration (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
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

theorem adaptive_cost_condition (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
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

def actions (A : Parameters ι) (n : ℕ → ℕ) (default : ι) (B : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℕ → ι :=
  ScheduledExecution.trajectory default (fun b ↦ n b+1)
    (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) B x

theorem costs_eq_scheduled (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (default : ι) (B b : ℕ) (hb : b<B)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    A.costs n loss default B b x=
      scheduledBlockCost (fun b ↦ n b+1) loss (A.actions n default B x) b := by
  unfold actions
  rw [ScheduledExecution.scheduledCost_eq_local default (fun b ↦ n b+1)
    (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) loss b B hb x]
  simp only [costs,dite_eq_left hb]
  rfl

theorem adaptive_regret_sum (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B : ℕ)
    (hn : ∀ b ∈ Finset.range B, n b+1≤horizon A.m) :
    let P := A.algorithm n loss hloss
    (∫ x, pathRegret (prefixHorizon (fun b ↦ n b+1) B) loss (A.actions n default B x)
      ∂(P.execution B).toMeasure)≤
        Real.log (Fintype.card ι:ℝ)/learningRate (Fintype.card ι) A.T A.m+
          (∑ b ∈ Finset.range B, (A.charge n b+
            (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m))+
          (prefixHorizon (fun b ↦ n b+1) B:ℝ)/(A.T:ℝ) := by
  let P := A.algorithm n loss hloss
  let μ := (P.execution B).toMeasure
  let length := fun b ↦ n b+1
  let η := learningRate (Fintype.card ι) A.T A.m
  let ε := 1/(A.T:ℝ)
  let g := P.estimates B
  let ξ := A.bias n loss hloss B
  let σ := fun b (_x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) ↦ A.charge n b
  have hcosteq (b : ℕ) (hb : b∈Finset.range B) :
      (fun x ↦ scheduledBlockCost length loss (A.actions n default B x) b)=A.costs n loss default B b := by
    funext x
    exact (A.costs_eq_scheduled n loss default B b (Finset.mem_range.mp hb) x).symm
  have hpast (b : ℕ) (hb : b∈Finset.range B) (t : ℕ) (ht : t<b) (i : ι) :
      AEStronglyMeasurable[AdaptiveEW.histories B b] (fun x ↦ g t x i) μ := by
    rw [AdaptiveEW.histories_of_le (Y := fun b ↦ DyadicBlockOutcome ι A.m (n b)) B b (by
      have := Finset.mem_range.mp hb
      omega)]
    exact P.estimates_adapted b B (by have := Finset.mem_range.mp hb; omega) t ht i
  have hbound : ∀ᵐ x ∂μ, ∀ b ∈ Finset.range B, η*‖g b x‖≤1 := by
    apply Eventually.of_forall
    intro x b hb
    exact A.adaptive_estimate_range n loss hloss B b (Finset.mem_range.mp hb) x
  have hcost (b : ℕ) (hb : b∈Finset.range B) :
      μ[fun x ↦ scheduledBlockCost length loss (A.actions n default B x) b | AdaptiveEW.histories B b] ≤ᵐ[μ]
        fun x ↦ (smoothedWeights η g ε A.smoothing_nonneg (by linarith [A.smoothing_le_half]) b x).mean
          (scheduledBlockLoss length loss b)+σ b x-
            2*η*(μ[fun y ↦ (smoothedWeights η g ε A.smoothing_nonneg (by linarith [A.smoothing_le_half]) b y).squareNorm
              (g b y) | AdaptiveEW.histories B b]) x := by
    rw [hcosteq b hb]
    exact A.adaptive_cost_condition n loss hloss default B b (Finset.mem_range.mp hb) (hn b hb)
  have hreg := self_financing_regret μ η
    (learningRate_pos A.card_ge_two A.time_ge_two A.bands_ge_five)
    ε A.smoothing_nonneg A.smoothing_le_half B length (fun b _ ↦ Nat.succ_pos (n b)) loss hloss
    (A.actions n default B) g ξ σ (AdaptiveEW.histories B) (fun _ _ ↦ le_top) hpast
    (fun _ _ _ ↦ (measurable_of_finite _).stronglyMeasurable.aestronglyMeasurable) hbound
    (fun _ _ ↦ (measurable_of_finite _).stronglyMeasurable.aestronglyMeasurable)
    (measurable_of_finite _).stronglyMeasurable.aestronglyMeasurable
    (fun _ _ ↦ integrable_const _)
    (fun b hb i ↦ A.adaptive_calibration n loss hloss default B b (Finset.mem_range.mp hb) (hn b hb) i) hcost
  have hcharges (b : ℕ) (hb : b∈Finset.range B) :
      (∫ x, (σ b x+2*‖ξ b x‖) ∂μ)≤A.charge n b+
        (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m := by
    have hp (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
        σ b x+2*‖ξ b x‖≤A.charge n b+
          (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m := by
      have hx := A.adaptive_bias_bound n loss hloss default B b (hn b hb) x
      change ‖ξ b x‖≤_ at hx
      dsimp only [σ]
      calc
        _ ≤ A.charge n b+2*((2:ℝ)^6*failure (Fintype.card ι) A.T*
            ((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m) := by linarith only [hx]
        _ = _ := by norm_num; ring
    have hi := integral_mono_ae (Integrable.of_finite (μ := μ) (f := fun x ↦ σ b x+2*‖ξ b x‖))
      (integrable_const (μ := μ) _) (Eventually.of_forall hp)
    simpa only [integral_const,probReal_univ,one_smul] using hi
  have hsum := Finset.sum_le_sum hcharges
  change (∫ x, pathRegret (prefixHorizon length B) loss (A.actions n default B x) ∂μ)≤_
  calc
    _ ≤ Real.log (Fintype.card ι:ℝ)/η+(∑ b ∈ Finset.range B, ∫ x, (σ b x+2*‖ξ b x‖) ∂μ)+
        ε*(prefixHorizon length B:ℝ) := hreg
    _ ≤ Real.log (Fintype.card ι:ℝ)/η+(∑ b ∈ Finset.range B,
        (A.charge n b+(2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m))+
          ε*(prefixHorizon length B:ℝ) := by linarith
    _ = _ := by dsimp only [ε]; ring

def switchCharges (A : Parameters ι) (n : ℕ → ℕ) (default : ι) (B b : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℝ :=
  if h : b<B then blockInternalSwitches default (past (b+1) B (by omega) x).2+1 else 0

theorem adaptive_switch_sum (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B : ℕ)
    (hn : ∀ b ∈ Finset.range B, n b+1≤horizon A.m) :
    let P := A.algorithm n loss hloss
    (∫ x, (switchCount (prefixHorizon (fun b ↦ n b+1) B) (A.actions n default B x):ℝ)
      ∂(P.execution B).toMeasure)≤(B:ℝ)+2*meanRate A.m*(prefixHorizon (fun b ↦ n b+1) B:ℝ) := by
  let P := A.algorithm n loss hloss
  let μ := (P.execution B).toMeasure
  let length := fun b ↦ n b+1
  have hblock (b : ℕ) (hb : b∈Finset.range B) :
      (∫ x, A.switchCharges n default B b x ∂μ)≤1+2*meanRate A.m*((n b:ℝ)+1) := by
    have hb' : b<B := Finset.mem_range.mp hb
    let fS := fun s : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) (b+1) ↦
      blockInternalSwitches default s.2+1
    have heq : A.switchCharges n default B b=(fun x ↦ fS (past (b+1) B (by omega) x)) := by
      funext x
      simp only [switchCharges,dite_eq_left hb']
      rfl
    rw [heq]
    change (∫ x, fS (past (b+1) B (by omega) x) ∂(law P.kernel B).toMeasure)≤_
    rw [integral_next P.kernel b B (by omega) fS]
    calc
      _ ≤ (law P.kernel b).mean (fun _ ↦ 1+2*meanRate A.m*((n b:ℝ)+1)) := by
        apply ProbabilityVector.mean_mono
        intro s
        exact (A.playedRow_guarantee n loss hloss default b (hn b hb) (P.distribution b s)).switches
      _ = _ := ProbabilityVector.mean_const _ _
  have hpoint (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
      (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)≤
        ∑ b ∈ Finset.range B, A.switchCharges n default B b x := by
    have hs := scheduledSwitches_cover length B (A.actions n default B x)
    have hsr : (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)≤
        ∑ b ∈ Finset.range B, ((switchCount (length b)
          (fun t ↦ A.actions n default B x (prefixHorizon length b+t)):ℝ)+1) := by
      exact_mod_cast hs
    calc
      _ ≤ _ := hsr
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        have hb' : b<B := Finset.mem_range.mp hb
        simp only [switchCharges,dite_eq_left hb']
        have hlocal := ScheduledExecution.scheduledSwitches_eq_local default length
          (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) b B hb' x
        exact congrArg (fun q : ℕ ↦ (q:ℝ)+1) hlocal
  have hInt := integral_mono_ae
    (Integrable.of_finite (μ := μ) (f := fun x ↦ (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)))
    (Integrable.of_finite (μ := μ) (f := fun x ↦ ∑ b ∈ Finset.range B, A.switchCharges n default B b x))
    (Eventually.of_forall hpoint)
  rw [integral_finsetSum _ (fun b _ ↦ Integrable.of_finite (μ := μ) (f := A.switchCharges n default B b))] at hInt
  calc
    _ ≤ ∑ b ∈ Finset.range B, ∫ x, A.switchCharges n default B b x ∂μ := hInt
    _ ≤ ∑ b ∈ Finset.range B, (1+2*meanRate A.m*((n b:ℝ)+1)) := Finset.sum_le_sum hblock
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
        ← Finset.mul_sum]
      have hlength : (∑ b ∈ Finset.range B, ((n b:ℝ)+1))=(prefixHorizon length B:ℝ) := by
        simp [prefixHorizon,length]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hlength
      rw [hlength]

theorem adaptive_fixed_rate_bound (A : Parameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B : ℕ)
    (hn : ∀ b ∈ Finset.range B, n b+1≤horizon A.m)
    (htotal : prefixHorizon (fun b ↦ n b+1) B=A.T)
    (hcount : (B:ℝ)≤8*DyadicRate.base A.m*(A.T:ℝ)+1)
    (hκ : 1/(A.T:ℝ)≤DyadicRate.base A.m) :
    let P := A.algorithm n loss hloss
    (∫ x, pathRegret A.T loss (A.actions n default B x) ∂(P.execution B).toMeasure)≤
        (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
          Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m+14*meanRate A.m*(A.T:ℝ)+3 ∧
      (∫ x, (switchCount A.T (A.actions n default B x):ℝ) ∂(P.execution B).toMeasure)≤
        10*meanRate A.m*(A.T:ℝ)+1 := by
  let P := A.algorithm n loss hloss
  let length := fun b ↦ n b+1
  let rare := ∑ b ∈ Finset.range B, (failure (Fintype.card ι) A.T*((n b:ℝ)+1)^3+
    (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m)
  have hrare : rare<1 := by
    simpa only [length,rare,Nat.cast_add,Nat.cast_one] using
      total_rare_charge_lt_one A.card_ge_two A.time_ge_two hκ length B htotal
  have hlen : (∑ b ∈ Finset.range B, ((n b:ℝ)+1))=(A.T:ℝ) := by
    have h := congrArg (fun q : ℕ ↦ (q:ℝ)) htotal
    simpa [prefixHorizon] using h
  have hcharges : (∑ b ∈ Finset.range B, (A.charge n b+
      (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m))=
      (B:ℝ)+6*meanRate A.m*(A.T:ℝ)+rare := by
    calc
      _ = ∑ b ∈ Finset.range B, ((1+6*meanRate A.m*((n b:ℝ)+1))+
          (failure (Fintype.card ι) A.T*((n b:ℝ)+1)^3+
            (2:ℝ)^7*failure (Fintype.card ι) A.T*((n b:ℝ)+1)*logScale (Fintype.card ι) A.T/DyadicRate.base A.m)) := by
        apply Finset.sum_congr rfl
        intro b _
        unfold charge
        ring
      _ = _ := by
        change _=(B:ℝ)+6*meanRate A.m*(A.T:ℝ)+∑ b ∈ Finset.range B, _
        rw [Finset.sum_add_distrib]
        congr 1
        calc
          _ = (B:ℝ)+6*meanRate A.m*(∑ b ∈ Finset.range B, ((n b:ℝ)+1)) := by
            rw [Finset.sum_add_distrib,← Finset.mul_sum]
            simp
          _ = _ := by rw [hlen]
  have hcμ : (B:ℝ)≤8*meanRate A.m*(A.T:ℝ)+1 := by
    have hh := mul_le_mul_of_nonneg_right (base_le_meanRate A.m) (show (0:ℝ)≤(A.T:ℝ) by positivity)
    linarith
  have hcomp : Real.log (Fintype.card ι:ℝ)/learningRate (Fintype.card ι) A.T A.m=
      (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
        Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m := by
    unfold learningRate
    rw [div_div_eq_mul_div]
    ring
  have hT0 : (A.T:ℝ)≠0 := by exact_mod_cast (show A.T≠0 by have := A.time_ge_two; omega)
  have hreg := A.adaptive_regret_sum n loss hloss default B hn
  rw [htotal,hcharges,div_self hT0,hcomp] at hreg
  have hswitch := A.adaptive_switch_sum n loss hloss default B hn
  rw [htotal] at hswitch
  constructor <;> linarith

def schedule (A : Parameters ι) : ℕ → ℕ := UniformSchedule.transitions A.T (horizon A.m)

def blockCount (A : Parameters ι) : ℕ := UniformSchedule.count A.T (horizon A.m)

theorem fixed_rate_execution (A : Parameters ι) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι)
    (hκ : 1/(A.T:ℝ)≤DyadicRate.base A.m) :
    let P := A.algorithm A.schedule loss hloss
    (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
          Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m+14*meanRate A.m*(A.T:ℝ)+3 ∧
      (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)
        ∂(P.execution A.blockCount).toMeasure)≤10*meanRate A.m*(A.T:ℝ)+1 := by
  have hH : 0<horizon A.m := by unfold horizon; positivity
  exact A.adaptive_fixed_rate_bound A.schedule loss hloss default A.blockCount
    (fun b _ ↦ UniformSchedule.length_le A.T (horizon A.m) b hH)
    (UniformSchedule.total A.T (horizon A.m) hH)
    (uniform_count_bound A.bands_ge_five A.T) hκ

theorem tuned_small_target (A : Parameters ι)
    (hm : A.m=exponent (target (Fintype.card ι) A.T))
    (hr : target (Fintype.card ι) A.T≤1/32)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) :
    let P := A.algorithm A.schedule loss hloss
    (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^40*min (A.T:ℝ) (performanceScale (Fintype.card ι) A.T) ∧
      (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)
        ∂(P.execution A.blockCount).toMeasure)≤
          (2:ℝ)^40*min (A.T:ℝ) (performanceScale (Fintype.card ι) A.T) := by
  let P := A.algorithm A.schedule loss hloss
  let μ := (P.execution A.blockCount).toMeasure
  let q := performanceScale (Fintype.card ι) A.T
  have hq : 4<q := performanceScale_gt_four A.card_ge_two A.time_ge_two
  have hκ : 1/(A.T:ℝ)≤DyadicRate.base A.m := by
    rw [hm]
    exact (tuned_parameters A.card_ge_two A.time_ge_two hr).2.2.2.1
  have hf := A.fixed_rate_execution loss hloss default hκ
  have hc : (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
      Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m≤(2:ℝ)^26*2000*q := by
    rw [hm]
    exact tuned_comparison_term A.card_ge_two A.time_ge_two hr
  have hμ : meanRate A.m*(A.T:ℝ)≤4*q := by
    rw [hm]
    exact tuned_meanRate A.card_ge_two A.time_ge_two hr
  have hRscale : (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤(2:ℝ)^40*q := by
    norm_num at hc ⊢
    linarith [hf.1]
  have hSscale : (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤(2:ℝ)^40*q := by
    norm_num
    linarith [hf.2]
  have hRtime : (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤2*(A.T:ℝ) := by
    have hp (x : History (fun b ↦ DyadicBlockOutcome ι A.m (A.schedule b)) A.blockCount) :
        pathRegret A.T loss (A.actions A.schedule default A.blockCount x)≤2*(A.T:ℝ) :=
      le_trans (le_abs_self _) (pathRegret_norm_le A.T loss hloss _)
    have h := integral_mono_ae (Integrable.of_finite (μ := μ)
      (f := fun x ↦ pathRegret A.T loss (A.actions A.schedule default A.blockCount x)))
      (integrable_const (μ := μ) (2*(A.T:ℝ))) (Eventually.of_forall hp)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hStime : (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤(A.T:ℝ) := by
    have hp (x : History (fun b ↦ DyadicBlockOutcome ι A.m (A.schedule b)) A.blockCount) :
        (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)≤(A.T:ℝ) := by
      exact_mod_cast le_trans (switchCount_le _ _) (Nat.sub_le A.T 1)
    have h := integral_mono_ae (Integrable.of_finite (μ := μ)
      (f := fun x ↦ (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)))
      (integrable_const (μ := μ) (A.T:ℝ)) (Eventually.of_forall hp)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hT : (0:ℝ)≤(A.T:ℝ) := by positivity
  change (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤
      (2:ℝ)^40*min (A.T:ℝ) q ∧
    (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤
      (2:ℝ)^40*min (A.T:ℝ) q
  rw [mul_min_of_nonneg (A.T:ℝ) q (by norm_num : (0:ℝ)≤2^40)]
  constructor
  · exact le_min (by norm_num; linarith) hRscale
  · exact le_min (by norm_num; linarith) hSscale

end Parameters

structure OptimalFamily (S : SteeringParameters ι) where
  assignment : (π : ProbabilityVector ι) → ComparisonAssignment S.tournament
    (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega))
  optimal : ∀ π, ∀ B : ComparisonAssignment S.tournament
      (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega)),
    (assignment π).totalWeight ≤ B.totalWeight

def ofOptimalFamily (S : SteeringParameters ι) (F : OptimalFamily S) : Parameters ι where
  toSteeringParameters := S
  preparation π :=
    let A := F.assignment π
    let H := A.preparedFamily (S.anchor π) (S.anchor_pos π) (DyadicRate.base S.m)
      (DyadicRate.base_pos S.m) (base_le_one_thirtytwo S.bands_ge_five)
    { holding := H
      rules := fun j => tournamentScoreRule S.tournament S.isTournament _ _ H.sampling_pos
        (H.kernel_reversible (DyadicRate.rate_pos S.m j))
        (H.kernel_holding_ge_half (DyadicRate.rate_pos S.m j))
      estimator := A.estimator (S.anchor π) H.sampling
      observable := (OptimizerTransfer.rounded_inputs_for_optimizer S.tournament S.isTournament
        (S.anchor π) (S.anchor_pos π) S.T S.card_ge_two S.time_ge_two (S.anchor_floor π)
        S.m S.bands_ge_five A (F.optimal π)).2.2.2.2.2.observable
      guarantee := OptimizerTransfer.rounded_block_guarantee_for_optimizer S.tournament S.isTournament
        (S.anchor π) (S.anchor_pos π) S.T S.card_ge_two S.time_ge_two (S.anchor_floor π)
        S.m S.bands_ge_five A (F.optimal π) }

theorem optimal_family_fixed_rate (S : SteeringParameters ι) (F : OptimalFamily S)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι)
    (hκ : 1/(S.T:ℝ)≤DyadicRate.base S.m) :
    let A := ofOptimalFamily S F
    let P := A.algorithm A.schedule loss hloss
    (∫ x, pathRegret S.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^25*threshold (Fintype.card ι) S.T*(S.m:ℝ)*logScale (Fintype.card ι) S.T*
          Real.log (Fintype.card ι:ℝ)/DyadicRate.base S.m+14*meanRate S.m*(S.T:ℝ)+3 ∧
    (∫ x, (switchCount S.T (A.actions A.schedule default A.blockCount x):ℝ)
      ∂(P.execution A.blockCount).toMeasure)≤10*meanRate S.m*(S.T:ℝ)+1 :=
  (ofOptimalFamily S F).fixed_rate_execution loss hloss default hκ

theorem optimal_family_tuned (S : SteeringParameters ι) (F : OptimalFamily S)
    (hm : S.m=exponent (target (Fintype.card ι) S.T))
    (hr : target (Fintype.card ι) S.T≤1/32)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) :
    let A := ofOptimalFamily S F
    let P := A.algorithm A.schedule loss hloss
    (∫ x, pathRegret S.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card ι) S.T) ∧
    (∫ x, (switchCount S.T (A.actions A.schedule default A.blockCount x):ℝ)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card ι) S.T) :=
  (ofOptimalFamily S F).tuned_small_target hm hr loss hloss default

end
end Tournament.Computation.OptimizerMainTransfer
