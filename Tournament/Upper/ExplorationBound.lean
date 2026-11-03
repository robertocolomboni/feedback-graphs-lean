module

public import Tournament.Upper.ExplorationDartboard

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory ShrinkingDartboard
open scoped Classical BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem expected_regret_budget (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0<η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (T : ℕ) (hT : 1≤T) (default : ι) :
    (execution E D κ hκ.le hκ1 η hη.le loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
      Real.log (Fintype.card ι:ℝ)/η+η*(T:ℝ)*(1+(D.card:ℝ)/(2*κ))+3*κ*(T:ℝ) := by
  let hn := fun n i ↦ (hloss n i).1
  let μ := execution E D κ hκ.le hκ1 η hη.le loss hn T
  let g := estimatesOnExecution E D κ hκ.le loss hn T
  let I := fun n x ↦ latentAt D default T x n
  have hSdb := actual_dartboard_guarantee E D κ hκ.le hκ1 η hη loss hn T hT default
  have hCurrent (n : ℕ) (hn : n∈Finset.range T) :
      HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ.toMeasure :=
    hSdb.1 n (Finset.mem_range.mp hn)
  have hQuad : μ.mean (quadraticTotal η g T)≤(T:ℝ)*(D.card:ℝ)/κ := by
    change μ.mean (fun x ↦ ∑ t∈Finset.range T, (randomWeights η g t x).squareNorm (fun i ↦ (g t x i : ℝ)))≤_
    rw [ProbabilityVector.mean_sum]
    calc
      _ ≤ ∑ _t∈Finset.range T, (D.card:ℝ)/κ := Finset.sum_le_sum (fun t ht ↦
        mean_weighted_secondMoment_le E D hD κ hκ hκ1 η hη.le loss hloss T t (Finset.mem_range.mp ht))
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have hWeight : μ.mean (fun x ↦ ∑ t∈Finset.range T, (randomWeights η g t x).mean (fun i ↦ (g t x i : ℝ)))≤(T:ℝ) := by
    rw [ProbabilityVector.mean_sum]
    calc
      _ ≤ ∑ _t∈Finset.range T, (1:ℝ) := Finset.sum_le_sum (fun t ht ↦
        mean_weighted_estimate_le_one E D hD κ hκ hκ1 η hη.le loss hloss T t (Finset.mem_range.mp ht))
      _ = _ := by simp
  have hSwitch := hSdb.2.2
  simp only [ProbabilityVector.integral_toMeasure] at hSwitch
  have hSwitchBound : μ.mean (fun x ↦ (Model.switchCount T (fun t ↦ I t x) : ℝ))≤η*(T:ℝ) :=
    hSwitch.trans (mul_le_mul_of_nonneg_left hWeight hη.le)
  obtain ⟨i,hBest⟩ := Model.exists_bestFixedLoss T loss
  have hEW := expected_second_order_finite μ.toMeasure g (fun _ ↦ measurable_of_finite _)
    I (fun _ ↦ measurable_of_finite _) η hη T hCurrent (fun _ _ _ ↦ Integrable.of_finite) Integrable.of_finite i
  simp only [ProbabilityVector.integral_toMeasure] at hEW
  have hSelected : μ.mean (fun x ↦ ∑ t∈Finset.range T, (g t x (I t x) : ℝ))=
      μ.mean (fun x ↦ Model.accumulatedLoss T loss (fun t ↦ I t x)) := by
    rw [ProbabilityVector.mean_sum]
    change _=μ.mean (fun x ↦ ∑ t∈Finset.range T, loss t (I t x))
    rw [ProbabilityVector.mean_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact mean_estimate_selected E D hD κ hκ hκ1 η hη.le loss hn T t (Finset.mem_range.mp ht) default
  have hComparator : μ.mean (fun x ↦ ∑ t∈Finset.range T, (g t x i : ℝ))=Model.fixedLoss T loss i := by
    rw [ProbabilityVector.mean_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact mean_estimate_coordinate E D hD κ hκ hκ1 η hη.le loss hn T t (Finset.mem_range.mp ht) i
  rw [hSelected,hComparator] at hEW
  have hLoss : μ.mean (fun x ↦ Model.accumulatedLoss T loss (fun t ↦ I t x))-Model.fixedLoss T loss i≤
      Real.log (Fintype.card ι:ℝ)/η+(η/2)*((T:ℝ)*(D.card:ℝ)/κ) :=
    hEW.trans (by
      have hm := mul_le_mul_of_nonneg_left hQuad (show 0≤η/2 by positivity)
      linarith)
  calc
    _ ≤ μ.mean (fun x ↦ Model.pathRegret T loss (latentAt D default T x))+3*κ*(T:ℝ) :=
      expected_exploration_regret_transfer E D κ hκ.le hκ1 η hη.le loss hloss T default
    _ ≤ Real.log (Fintype.card ι:ℝ)/η+(η/2)*((T:ℝ)*(D.card:ℝ)/κ)+η*(T:ℝ)+3*κ*(T:ℝ) := by
      change μ.mean (fun x ↦ (Model.accumulatedLoss T loss (fun t ↦ I t x)+
        (Model.switchCount T (fun t ↦ I t x):ℝ))-Model.bestFixedLoss T loss)+3*κ*(T:ℝ)≤_
      rw [ProbabilityVector.mean_sub,ProbabilityVector.mean_add,ProbabilityVector.mean_const,hBest]
      linarith
    _ = _ := by ring

theorem expected_regret_simplified (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκhalf : κ≤1/2) (η : ℝ) (hη : 0<η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (T : ℕ) (hT : 1≤T) (default : ι) :
    (execution E D κ hκ.le (by linarith) η hη.le loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
      Real.log (Fintype.card ι:ℝ)/η+η*(T:ℝ)*(D.card:ℝ)/κ+3*κ*(T:ℝ) := by
  have hd : (1:ℝ)≤(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  exact (expected_regret_budget E D hD κ hκ (by linarith) η hη loss hloss T hT default).trans
    (unsimplified_budget_le (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ) κ η hd
      (Nat.cast_nonneg _) hκ hκhalf hη.le)

theorem observable_graph_upper (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (default : ι) :
    let κ := rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    let η := learningRate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    ∃ hκ : 0<κ, ∃ hη : 0<η,
      (execution E D κ hκ.le (by linarith) η hη.le loss (fun n i ↦ (hloss n i).1) T).mean
        (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
        (3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  have hD0 : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  have hL : 0<Real.log (Fintype.card ι:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<Fintype.card ι))
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  let κ := rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
  let η := learningRate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
  have hκ : 0<κ := rate_pos _ _ _ hD0 hL hT0
  have hη : 0<η := learningRate_pos _ _ _ hD0 hL hT0
  refine ⟨hκ,hη,?_⟩
  calc
    _ ≤ Real.log (Fintype.card ι:ℝ)/η+η*(T:ℝ)*(D.card:ℝ)/κ+3*κ*(T:ℝ) :=
      expected_regret_simplified E D hD κ hκ hRate η hη loss hloss T hT default
    _ = 9*κ*(T:ℝ) := tuned_budget _ _ _ hD0 hL hT0
    _ = _ := final_constant _ _ _ hD0 hL hT0

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem observable_graph_large_rate (E : ι → ι → Prop) (D : Finset ι) (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : 1/2<rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ))
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (default : ι) :
    Model.pathRegret T loss (fun _ ↦ default)≤
      ((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  have hD0 : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  have hL : 0<Real.log (Fintype.card ι:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<Fintype.card ι))
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  exact (Model.constant_action_regret_le_horizon T loss default
    (fun t _ i ↦ (hloss t i).1) (fun t _ i ↦ (hloss t i).2)).trans
      (large_rate_fixed_action _ _ _ hD0 hL hT0 hRate)

end
end Tournament.Upper.Exploration
