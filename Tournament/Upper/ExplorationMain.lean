module

public import Tournament.Upper.ExplorationFeedbackMeasurable

@[expose] public section

namespace Tournament.Model

open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem pathRegret_eq_of_prefix (T : ℕ) (loss other : ℕ → ι → ℝ)
    (hPast : ∀ t<T, loss t=other t) (path : ℕ → ι) :
    pathRegret T loss path=pathRegret T other path := by
  have hA : accumulatedLoss T loss path=accumulatedLoss T other path := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hPast t (Finset.mem_range.mp ht)]
  have hF : fixedLoss T loss=fixedLoss T other := by
    funext i
    apply Finset.sum_congr rfl
    intro t ht
    rw [hPast t (Finset.mem_range.mp ht)]
  have hB : bestFixedLoss T loss=bestFixedLoss T other := by
    unfold bestFixedLoss
    rw [hF]
  unfold pathRegret
  rw [hA,hB]

end
end Tournament.Model

namespace Tournament.Upper.Exploration

open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem feedbackRecord_eq_of_past (E : ι → ι → Prop) (D : Finset ι) (loss other : ℕ → ι → ℝ)
    (n : ℕ) (hPast : ∀ t<n, loss t=other t) (h : History D n) :
    feedbackRecord E D loss n h=feedbackRecord E D other n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [feedbackRecord]
    rw [ih (fun t ht ↦ hPast t (by omega)) h.1,hPast n (by omega)]

theorem feedbackExecution_eq_of_past (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss other : ℕ → ι → ℝ) (T : ℕ) (hPast : ∀ t<T, loss t=other t) :
    feedbackExecution E D κ hκ hκ1 η hη loss T=feedbackExecution E D κ hκ hκ1 η hη other T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    change (feedbackExecution E D κ hκ hκ1 η hη loss T).joint
      (fun h ↦ feedbackRound E D κ hκ hκ1 η hη T h (feedbackRecord E D loss T h))=
      (feedbackExecution E D κ hκ hκ1 η hη other T).joint
        (fun h ↦ feedbackRound E D κ hκ hκ1 η hη T h (feedbackRecord E D other T h))
    rw [ih (fun t ht ↦ hPast t (by omega))]
    congr 1
    funext h
    rw [feedbackRecord_eq_of_past E D loss other T (fun t ht ↦ hPast t (by omega)) h]

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem observable_graph_lazy_exploration (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2) (default : ι) :
    let κ := rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    let η := learningRate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    ∃ hκ : 0<κ, ∃ hη : 0<η, ∀ loss : ℕ → ι → ℝ, (∀ t<T, BoundedLoss (loss t)) →
      (feedbackExecution E D κ hκ.le (by linarith) η hη.le loss T).mean
        (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
        (3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  have hD0 : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  have hL : 0<Real.log (Fintype.card ι:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<Fintype.card ι))
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hκ := rate_pos _ _ _ hD0 hL hT0
  have hη := learningRate_pos _ _ _ hD0 hL hT0
  refine ⟨hκ,hη,?_⟩
  intro loss hloss
  let padded : ℕ → ι → ℝ := fun t i ↦ if t<T then loss t i else 0
  have hPad : ∀ t, BoundedLoss (padded t) := by
    intro t i
    by_cases ht : t<T
    · simpa only [padded,ite_eq_left ht] using hloss t ht i
    · simp only [padded,ite_eq_right ht]
      constructor <;> norm_num
  have hPast : ∀ t<T, padded t=loss t := by
    intro t ht
    funext i
    simp only [padded,ite_eq_left ht]
  rcases observable_graph_feedback_upper E D hD hK T hT hRate padded hPad default with ⟨_,_,hBound⟩
  rw [feedbackExecution_eq_of_past E D _ hκ.le _ _ hη.le padded loss T hPast] at hBound
  have hReg : (fun x : History D T ↦ Model.pathRegret T padded (actions D default T x))=
      fun x ↦ Model.pathRegret T loss (actions D default T x) := by
    funext x
    exact Model.pathRegret_eq_of_prefix T padded loss hPast _
  rwa [hReg] at hBound

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem observable_graph_large_rate_finite (E : ι → ι → Prop) (D : Finset ι) (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : 1/2<rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ))
    (loss : ℕ → ι → ℝ) (hloss : ∀ t<T, BoundedLoss (loss t)) (default : ι) :
    Model.pathRegret T loss (fun _ ↦ default)≤
      ((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  have hD0 : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  have hL : 0<Real.log (Fintype.card ι:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<Fintype.card ι))
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  exact (Model.constant_action_regret_le_horizon T loss default
    (fun t ht i ↦ (hloss t ht i).1) (fun t ht i ↦ (hloss t ht i).2)).trans
      (large_rate_fixed_action _ _ _ hD0 hL hT0 hRate)

end
end Tournament.Upper.Exploration
