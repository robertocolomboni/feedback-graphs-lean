module

public import Tournament.Upper.AdaptiveSwitches
public import Tournament.Upper.FixedRateArithmetic

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem adaptive_fixed_rate_bound (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
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

def schedule (A : SteeringParameters ι) : ℕ → ℕ := UniformSchedule.transitions A.T (horizon A.m)

def blockCount (A : SteeringParameters ι) : ℕ := UniformSchedule.count A.T (horizon A.m)

theorem fixed_rate_execution (A : SteeringParameters ι) (loss : ℕ → ι → ℝ)
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

end
end Tournament.Upper.SteeringParameters
