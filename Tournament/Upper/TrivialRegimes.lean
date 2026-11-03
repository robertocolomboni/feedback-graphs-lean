module

public import Tournament.Model.GraphStrategy
public import Tournament.Upper.Tuning

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open Model BlockParameters Tuning

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem fixed_action_large_target (E : ι → ι → Prop) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hr : 1/32<target (Fintype.card ι) T) (default : ι) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) :
    (GraphStrategy.constant default).regret E T loss≤(2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) ∧
      (GraphStrategy.constant default).switches E T loss≤(2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) := by
  have hreg := constant_action_regret_le_horizon T loss default
    (fun t _ i ↦ (hloss t i).1) (fun t _ i ↦ (hloss t i).2)
  have hlarge := large_target_fixed_action hK hT hr
  have hq := performanceScale_gt_four hK hT
  have ht : (0:ℝ)≤(T:ℝ) := by positivity
  rw [GraphStrategy.regret_constant,GraphStrategy.switches_constant,
    mul_min_of_nonneg (T:ℝ) (performanceScale (Fintype.card ι) T) (by norm_num : (0:ℝ)≤2^40)]
  constructor <;> apply le_min <;> norm_num <;> linarith

theorem fixed_action_time_one (E : ι → ι → Prop) (hK : 2≤Fintype.card ι)
    (default : ι) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    (GraphStrategy.constant default).regret E 1 loss≤(2:ℝ)^40*min (1:ℝ) (performanceScale (Fintype.card ι) 1) ∧
      (GraphStrategy.constant default).switches E 1 loss≤(2:ℝ)^40*min (1:ℝ) (performanceScale (Fintype.card ι) 1) := by
  have hq := performanceScale_time_one hK
  have hreg := constant_action_regret_le_horizon 1 loss default
    (fun t _ i ↦ (hloss t i).1) (fun t _ i ↦ (hloss t i).2)
  rw [GraphStrategy.regret_constant,GraphStrategy.switches_constant,min_eq_left hq]
  norm_num
  norm_num at hreg
  linarith

theorem fixed_action_card_one (E : ι → ι → Prop) (T : ℕ) (hK : Fintype.card ι=1)
    (default : ι) (loss : ℕ → ι → ℝ) :
    (GraphStrategy.constant default).regret E T loss≤(2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) ∧
      (GraphStrategy.constant default).switches E T loss≤(2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) := by
  have : Subsingleton ι := (Fintype.card_le_one_iff_subsingleton).mp (by omega)
  have hbest : bestFixedLoss T loss=fixedLoss T loss default := by
    obtain ⟨i,hi⟩ := exists_bestFixedLoss T loss
    simpa only [Subsingleton.elim i default] using hi
  have hzero : pathRegret T loss (fun _ ↦ default)=0 := by
    unfold pathRegret
    rw [switchCount_constant,hbest]
    simp only [Nat.cast_zero,add_zero,accumulatedLoss,fixedLoss,sub_self]
  rw [GraphStrategy.regret_constant,GraphStrategy.switches_constant,hzero]
  have hnonneg : (0:ℝ)≤performanceScale (Fintype.card ι) T := by unfold performanceScale; positivity
  have hmin : (0:ℝ)≤min (T:ℝ) (performanceScale (Fintype.card ι) T) := le_min (by positivity) hnonneg
  constructor <;> positivity

end
end Tournament.Upper
