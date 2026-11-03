module

public import Tournament.Upper.AdaptiveCalibration
public import Tournament.Model.ScheduledExecution
public import Tournament.Upper.SelfFinancingRegret

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section

set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def actions (A : SteeringParameters ι) (n : ℕ → ℕ) (default : ι) (B : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℕ → ι :=
  ScheduledExecution.trajectory default (fun b ↦ n b+1)
    (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) B x

omit [Nonempty ι] in
theorem costs_eq_scheduled (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (default : ι) (B b : ℕ) (hb : b<B)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
    A.costs n loss default B b x=
      scheduledBlockCost (fun b ↦ n b+1) loss (A.actions n default B x) b := by
  unfold actions
  rw [ScheduledExecution.scheduledCost_eq_local default (fun b ↦ n b+1)
    (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) loss b B hb x]
  simp only [costs,dite_eq_left hb]
  rfl

theorem adaptive_regret_sum (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
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

end
end Tournament.Upper.SteeringParameters
