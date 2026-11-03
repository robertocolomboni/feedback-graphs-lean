module

public import Tournament.Upper.SteeringPrivateBounds
public import Tournament.Upper.GraphTunedExecution
public import Tournament.Upper.TrivialRegimes

@[expose] public section

namespace Tournament.Upper

open MeasureTheory Model Model.MeasurableGame Tuning
open scoped Classical

noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι] [LinearOrder ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [Fintype ι] [Nonempty ι] [LinearOrder ι] [DiscreteMeasurableSpace ι] in
theorem constantStrategy_expectedSwitches (default : ι) (T : ℕ)
    (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (constantStrategy.{u,0} default).expectedSwitches T E loss = 0 := by
  change (∫ _ω : ULift.{0} Unit, (@switchCount ι (Classical.decEq ι) T (fun _ ↦ default) : ℝ)
    ∂(@Measure.dirac (ULift.{0} Unit) ⊤ (ULift.up ()))) = 0
  simp only [switchCount_constant, Nat.cast_zero, integral_zero]

def tournamentPrivateStrategy (E : ι → ι → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (default : ι) (rounded : Bool := false) : Strategy.{u,0} ι :=
  if hK : Fintype.card ι = 1 then constantStrategy default
  else if hT : 2 ≤ T then
    if hr : target (Fintype.card ι) T ≤ 1/32 then
      (graphTunedParameters E hE T (by have := Fintype.card_pos (α := ι); omega) hT hr rounded).seedStrategy default
    else constantStrategy default
  else constantStrategy default

theorem tournamentPrivateStrategy_bound (E : ι → ι → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1 ≤ T) (default : ι) (loss : ℕ → ι → ℝ)
    (hLoss : ∀ t, BoundedLoss (loss t)) (rounded : Bool := false) :
    (tournamentPrivateStrategy E hE T default rounded).regret T E loss ≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) ∧
      (tournamentPrivateStrategy E hE T default rounded).expectedSwitches T E loss ≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) := by
  unfold tournamentPrivateStrategy
  split
  · rename_i hK
    rw [constantStrategy_regret, constantStrategy_expectedSwitches]
    have h := fixed_action_card_one E T hK default loss
    simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
      pathRegret_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι)] using h
  · rename_i hK
    have hK2 : 2 ≤ Fintype.card ι := by have := Fintype.card_pos (α := ι); omega
    split
    · rename_i hT2
      split
      · rename_i hr
        exact (graphTunedParameters E hE T hK2 hT2 hr rounded).seedStrategy_tuned
          E rfl rfl hr default loss hLoss
      · rename_i hr
        rw [constantStrategy_regret, constantStrategy_expectedSwitches]
        have h := fixed_action_large_target E T hK2 hT2 (lt_of_not_ge hr) default loss hLoss
        simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
          pathRegret_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι)] using h
    · rename_i hT2
      have hTeq : T = 1 := by omega
      subst T
      rw [constantStrategy_regret, constantStrategy_expectedSwitches]
      have h := fixed_action_time_one E hK2 default loss hLoss
      simpa only [Nat.cast_one, GraphStrategy.regret_constant, GraphStrategy.switches_constant,
        pathRegret_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι)] using h

theorem stronglyRevealing_minimax_upper (E : ι → ι → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1 ≤ T) (rounded : Bool := false) :
    minimax.{u,0} T E ≤ (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) := by
  let default : ι := Classical.arbitrary ι
  apply (minimax_le_worst (tournamentPrivateStrategy E hE T default rounded) T E).trans
  apply Strategy.worstRegret_le
  intro loss hLoss
  exact (tournamentPrivateStrategy_bound E hE T hT default loss hLoss rounded).1

theorem stronglyRevealing_minimax_upper_explicit (E : ι → ι → Prop)
    (hE : StronglyRevealing E) (T : ℕ) (hT : 1 ≤ T) :
    minimax.{u,0} T E ≤
      (2:ℝ)^40*Real.sqrt ((T:ℝ)*Real.log (Fintype.card ι:ℝ))*
        (Real.log (Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ)))^2 := by
  have h := stronglyRevealing_minimax_upper E hE T hT
  have hle : (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) ≤
      (2:ℝ)^40*performanceScale (Fintype.card ι) T :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  exact h.trans (by simpa only [performanceScale, BlockParameters.logScale, mul_assoc] using hle)

end
end Tournament.Upper
