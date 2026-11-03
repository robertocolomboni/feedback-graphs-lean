module

public import Tournament.Probability.ProcessConditional
public import Tournament.Model.BlockAccounting

@[expose] public section

namespace Tournament.Model.ScheduledExecution

open scoped BigOperators Classical
open FiniteProcess

noncomputable section

universe u v
variable {Y : ℕ → Type u} {ι : Type v}

def trajectory (default : ι) (length : ℕ → ℕ) (localPath : (b : ℕ) → Y b → ℕ → ι) :
    (B : ℕ) → History Y B → ℕ → ι
  | 0, _ => fun _ ↦ default
  | B+1, x => appendActions (prefixHorizon length B)
      (trajectory default length localPath B x.1) (localPath B x.2)

theorem prefixHorizon_mono (length : ℕ → ℕ) (b B : ℕ) (h : b≤B) :
    prefixHorizon length b≤prefixHorizon length B := by
  induction B with
  | zero =>
    have hb : b=0 := by omega
    subst b
    rfl
  | succ B ih =>
    by_cases hb : b=B+1
    · subst b
      rfl
    · rw [prefixHorizon_succ]
      exact le_trans (ih (by omega)) (Nat.le_add_right _ _)

theorem trajectory_past (default : ι) (length : ℕ → ℕ) (localPath : (b : ℕ) → Y b → ℕ → ι)
    (b B : ℕ) (h : b≤B) (x : History Y B) (t : ℕ) (ht : t<prefixHorizon length b) :
    trajectory default length localPath B x t=
      trajectory default length localPath b (past b B h x) t := by
  induction B with
  | zero =>
    have hb : b=0 := by omega
    subst b
    rw [past_self]
  | succ B ih =>
    by_cases hb : b=B+1
    · subst b
      rw [past_self]
    · have hb' : b≤B := by omega
      have ht' : t<prefixHorizon length B := lt_of_lt_of_le ht (prefixHorizon_mono length b B hb')
      rw [trajectory,appendActions,ite_eq_left ht',past_succ b B hb']
      exact ih hb' x.1

theorem trajectory_block (default : ι) (length : ℕ → ℕ) (localPath : (b : ℕ) → Y b → ℕ → ι)
    (b B : ℕ) (h : b<B) (x : History Y B) (t : ℕ) (ht : t<length b) :
    trajectory default length localPath B x (prefixHorizon length b+t)=
      localPath b (past (b+1) B (by omega) x).2 t := by
  have htime : prefixHorizon length b+t<prefixHorizon length (b+1) := by
    rw [prefixHorizon_succ]
    omega
  rw [trajectory_past default length localPath (b+1) B (by omega) x _ htime,
    trajectory,appendActions,ite_eq_right (by omega : ¬prefixHorizon length b+t<prefixHorizon length b)]
  simp only [Nat.add_sub_cancel_left]

theorem scheduledSwitches_eq_local [DecidableEq ι] (default : ι) (length : ℕ → ℕ)
    (localPath : (b : ℕ) → Y b → ℕ → ι)
    (b B : ℕ) (h : b<B) (x : History Y B) :
    switchCount (length b) (fun t ↦ trajectory default length localPath B x (prefixHorizon length b+t))=
      switchCount (length b) (localPath b (past (b+1) B (by omega) x).2) := by
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t<length b-1 := Finset.mem_range.mp ht
  dsimp only
  simp only [trajectory_block default length localPath b B h x (t+1) (by omega),
    trajectory_block default length localPath b B h x t (by omega)]

theorem scheduledCost_eq_local [DecidableEq ι] (default : ι) (length : ℕ → ℕ)
    (localPath : (b : ℕ) → Y b → ℕ → ι) (loss : ℕ → ι → ℝ)
    (b B : ℕ) (h : b<B) (x : History Y B) :
    scheduledBlockCost length loss (trajectory default length localPath B x) b=
      accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
          (localPath b (past (b+1) B (by omega) x).2)+
        (switchCount (length b) (localPath b (past (b+1) B (by omega) x).2):ℝ)+1 := by
  have hL : accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
      (fun t ↦ trajectory default length localPath B x (prefixHorizon length b+t))=
      accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
        (localPath b (past (b+1) B (by omega) x).2) := by
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only
    rw [trajectory_block default length localPath b B h x t (Finset.mem_range.mp ht)]
  have hS := scheduledSwitches_eq_local default length localPath b B h x
  unfold scheduledBlockCost
  rw [hL,hS]

end
end Tournament.Model.ScheduledExecution
