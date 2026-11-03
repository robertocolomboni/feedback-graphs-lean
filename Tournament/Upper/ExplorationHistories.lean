module

public import Tournament.Upper.ExplorationConditional
public import Tournament.Probability.FreshIndependence

@[expose] public section

namespace Tournament.Upper.Exploration

open ShrinkingDartboard
open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def recordedEstimate (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (n : ℕ) (h : History D (n+1)) : LossVector ι :=
  fun i ↦ ⟨estimate E D κ (loss n) h.2.2 i,estimate_nonneg E D κ hκ (loss n) (hloss n) h.2.2 i⟩

def estimateHistory (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) :
    (n : ℕ) → History D n → LossHistory ι n
  | 0, _ => fun t ↦ Fin.elim0 t
  | n+1, h => Fin.snoc (estimateHistory E D κ hκ loss hloss n h.1)
      (recordedEstimate E D κ hκ loss hloss n h)

theorem historyWeights_estimateHistory (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ) (η : ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (n : ℕ) (h : History D n) :
    historyWeights η n (estimateHistory E D κ hκ loss hloss n h)=processWeights E D κ η loss n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [historyWeights,estimateHistory,Fin.init_snoc,Fin.snoc_last]
    rw [ih h.1]
    rfl

def estimatesOnExecution (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ)
    (n : ℕ) (x : History D T) : LossVector ι :=
  if hn : n<T then recordedEstimate E D κ hκ loss hloss n (FiniteProcess.past (n+1) T (by omega) x)
  else fun _ ↦ 0

omit [Fintype ι] [Nonempty ι] in
theorem estimateHistory_execution (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T n : ℕ) (hn : n≤T) (x : History D T) :
    lossHistory (estimatesOnExecution E D κ hκ loss hloss T) n x=
      estimateHistory E D κ hκ loss hloss n (FiniteProcess.past n T hn x) := by
  induction n with
  | zero =>
    funext t
    exact Fin.elim0 t
  | succ n ih =>
    have hnT : n<T := by omega
    have hPrefix : (FiniteProcess.past (n+1) T hn x).1=FiniteProcess.past n T (by omega) x := by
      have hc := FiniteProcess.past_comp n (n+1) T (by omega) hn x
      simpa only [FiniteProcess.past_succ n n le_rfl,FiniteProcess.past_self] using hc
    funext t
    refine Fin.lastCases ?_ (fun j ↦ ?_) t
    · simp only [lossHistory,estimatesOnExecution,dite_eq_left hnT,estimateHistory,Fin.snoc_last,Fin.val_last]
    · have h := congrFun (ih (by omega)) j
      simpa only [lossHistory,estimateHistory,Fin.snoc_castSucc,Function.comp_def,Fin.val_castSucc,hPrefix] using h

end
end Tournament.Upper.Exploration
