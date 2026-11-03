module

public import Tournament.Computation.OptimizerPrivateBounds
public import Tournament.Upper.SteeringMinimax

@[expose] public section

namespace Tournament.Computation.OptimizerMinimax

open MeasureTheory Upper Model MeasurableGame Tuning OptimizerCodeMeasurable
open scoped Classical
noncomputable section

variable {K : ℕ} [Nonempty (Fin K)]
local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b ↦ Classical.propDecidable (a=b)

def CorrectForGraph (solve : Candidate K) (E : Fin K → Fin K → Prop)
    (hE : StronglyRevealing E) (T : ℕ) : Prop :=
  ∀ (hK : 2≤Fintype.card (Fin K)) (hT : 2≤T)
    (hr : target (Fintype.card (Fin K)) T≤1/32),
    CorrectOnRounded (graphTunedParameters E hE T hK hT hr true) solve

def strategy (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (default : Fin K) (solve : Candidate K)
    (hc : CorrectForGraph solve E hE T) : Strategy.{0,0} (Fin K) :=
  if hK : Fintype.card (Fin K)=1 then constantStrategy default
  else if hT : 2≤T then
    if hr : target (Fintype.card (Fin K)) T≤1/32 then
      let hK2 : 2≤Fintype.card (Fin K) := by have := Fintype.card_pos (α := Fin K); omega
      OptimizerPrivateBounds.privateStrategy (graphTunedParameters E hE T hK2 hT hr true)
        solve (hc hK2 hT hr) default
    else constantStrategy default
  else constantStrategy default

theorem strategy_bound (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) (default : Fin K) (solve : Candidate K)
    (hc : CorrectForGraph solve E hE T) (loss : ℕ → Fin K → ℝ)
    (hLoss : ∀ t, BoundedLoss (loss t)) :
    (strategy E hE T default solve hc).regret T E loss ≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) ∧
    (strategy E hE T default solve hc).expectedSwitches T E loss ≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) := by
  unfold strategy
  split
  · rename_i hK
    rw [constantStrategy_regret, constantStrategy_expectedSwitches]
    have h := fixed_action_card_one E T hK default loss
    simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
      pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h
  · rename_i hK
    have hK2 : 2≤Fintype.card (Fin K) := by have := Fintype.card_pos (α := Fin K); omega
    split
    · rename_i hT2
      split
      · rename_i hr
        exact OptimizerPrivateBounds.tuned (graphTunedParameters E hE T hK2 hT2 hr true)
          solve (hc hK2 hT2 hr) E (selectedEdge_orientationObserved E) rfl hr default loss hLoss
      · rename_i hr
        rw [constantStrategy_regret, constantStrategy_expectedSwitches]
        have h := fixed_action_large_target E T hK2 hT2 (lt_of_not_ge hr) default loss hLoss
        simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
          pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h
    · rename_i hT2
      have hTeq : T=1 := by omega
      subst T
      rw [constantStrategy_regret, constantStrategy_expectedSwitches]
      have h := fixed_action_time_one E hK2 default loss hLoss
      simpa only [Nat.cast_one, GraphStrategy.regret_constant, GraphStrategy.switches_constant,
        pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h

theorem minimax_upper (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) (solve : Candidate K) (hc : CorrectForGraph solve E hE T) :
    minimax.{0,0} T E ≤ (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) := by
  let default : Fin K := Classical.arbitrary (Fin K)
  apply (minimax_le_worst (strategy E hE T default solve hc) T E).trans
  apply Strategy.worstRegret_le
  intro loss hLoss
  exact (strategy_bound E hE T hT default solve hc loss hLoss).1

end
end Tournament.Computation.OptimizerMinimax
