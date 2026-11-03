module

public import Tournament.Upper.DartboardConditionalKernel
public import Tournament.Model.SensorTranscript

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

abbrev LossVector (ι : Type*) := ι → ℝ≥0
abbrev LossHistory (ι : Type*) (n : ℕ) := Fin n → LossVector ι

def lossHistory {Ω : Type*} (g : ℕ → Ω → LossVector ι) (n : ℕ) (ω : Ω) : LossHistory ι n :=
  fun t ↦ g t.val ω

def appendLoss (n : ℕ) : (LossHistory ι n × LossVector ι) ≃ᵐ LossHistory ι (n+1) where
  toFun q := Fin.snoc q.1 q.2
  invFun h := (Fin.init h,h (Fin.last n))
  left_inv q := by simp only [Fin.init_snoc,Fin.snoc_last,Prod.mk.eta]
  right_inv h := Fin.snoc_init_self h
  measurable_toFun := Model.MeasurableGame.measurable_snoc _ _ measurable_fst measurable_snd
  measurable_invFun := (Measurable.of_eval (fun _ ↦ measurable_pi_apply _)).prodMk
    (measurable_pi_apply _)

def historyWeights (η : ℝ) : (n : ℕ) → LossHistory ι n → ProbabilityVector ι
  | 0, _ => ExponentialWeights.uniform
  | n+1, h => Model.exponentialUpdate (historyWeights η n (Fin.init h)) η
      (fun i ↦ (h (Fin.last n) i : ℝ))

theorem historyWeights_measurable (η : ℝ) (n : ℕ) (i : ι) :
    Measurable (fun h : LossHistory ι n ↦ historyWeights η n h i) := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (fun h : LossHistory ι (n+1) ↦ Fin.init h) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    exact update_weight_measurable (fun h : LossHistory ι (n+1) ↦ historyWeights η n (Fin.init h))
      (fun j ↦ (ih j).comp hinit) (fun h : LossHistory ι (n+1) ↦ fun j ↦ (h (Fin.last n) j : ℝ))
      (fun j ↦ measurable_coe_nnreal_real.comp ((measurable_pi_apply j).comp (measurable_pi_apply _))) η i

theorem previousWeights_measurable (η : ℝ) (n : ℕ) (i : ι) :
    Measurable (fun h : LossHistory ι (n+1) ↦ historyWeights η n (Fin.init h) i) :=
  (historyWeights_measurable η n i).comp (Measurable.of_eval (fun _ ↦ measurable_pi_apply _))

omit [Fintype ι] [Nonempty ι] in
theorem lastLoss_measurable (n : ℕ) (i : ι) :
    Measurable (fun h : LossHistory ι (n+1) ↦ (h (Fin.last n) i : ℝ)) :=
  measurable_coe_nnreal_real.comp ((measurable_pi_apply i).comp (measurable_pi_apply _))

omit [Fintype ι] [Nonempty ι] in
theorem lossHistory_measurable {Ω : Type*} [MeasurableSpace Ω] (g : ℕ → Ω → LossVector ι)
    (hg : ∀ n, Measurable (g n)) (n : ℕ) : Measurable (lossHistory g n) :=
  Measurable.of_eval (fun t ↦ hg t.val)

omit [Fintype ι] [Nonempty ι] in
theorem init_lossHistory {Ω : Type*} (g : ℕ → Ω → LossVector ι) (n : ℕ) (ω : Ω) :
    Fin.init (lossHistory g (n+1) ω)=lossHistory g n ω := rfl

omit [Fintype ι] [Nonempty ι] in
theorem last_lossHistory {Ω : Type*} (g : ℕ → Ω → LossVector ι) (n : ℕ) (ω : Ω) :
    lossHistory g (n+1) ω (Fin.last n)=g n ω := rfl

omit [Fintype ι] [Nonempty ι] in
theorem append_lossHistory {Ω : Type*} (g : ℕ → Ω → LossVector ι) (n : ℕ) :
    (appendLoss n) ∘ (fun ω ↦ (lossHistory g n ω,g n ω))=lossHistory g (n+1) := by
  funext ω
  exact Fin.snoc_init_self (lossHistory g (n+1) ω)

theorem historyWeights_eq_weights {Ω : Type*} (η : ℝ) (g : ℕ → Ω → LossVector ι)
    (n : ℕ) (ω : Ω) : historyWeights η n (lossHistory g n ω)=
      weights η (fun t i ↦ (g t ω i : ℝ)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Model.exponentialUpdate (historyWeights η n (lossHistory g n ω)) η (fun i ↦ (g n ω i : ℝ))=_
    rw [ih]
    rfl

end
end Tournament.Upper.ShrinkingDartboard
