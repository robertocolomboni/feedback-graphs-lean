module

public import Tournament.Probability.DyadicTrajectoryEncoding
public import Tournament.Model.ScheduledExecution

@[expose] public section

namespace Tournament.Upper

open Model
noncomputable section

variable {ι : Type*}

abbrev metadataHistory (m : ℕ) (n : ℕ → ℕ) (B : ℕ) :=
  FiniteProcess.History (fun b ↦ Fin (m+1) × Restarts.Coins (n b)) B

def trajectoryShuffle (A B C D : Type*) : (A × B) × (C × D) ≃ (A × C) × (B × D) where
  toFun q := ((q.1.1,q.2.1),(q.1.2,q.2.2))
  invFun q := ((q.1.1,q.2.1),(q.1.2,q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def executionTraceEquiv (m : ℕ) (n : ℕ → ℕ) : (B : ℕ) →
    FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B ≃
      (metadataHistory m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι))
  | 0 => {
      toFun := fun _ ↦ (ULift.up (),fun i ↦ Fin.elim0 i)
      invFun := fun _ ↦ ULift.up ()
      left_inv := fun h ↦ by rcases h with ⟨⟨⟩⟩; rfl
      right_inv := fun q ↦ by
        rcases q with ⟨⟨⟨⟩⟩,f⟩
        apply Prod.ext
        · rfl
        · funext i
          exact Fin.elim0 i }
  | B+1 =>
      (Equiv.prodCongr (executionTraceEquiv m n B) (dyadicTraceEquiv (ι := ι) m (n B))).trans
        ((trajectoryShuffle _ _ _ _).trans
          (Equiv.prodCongr (Equiv.refl _) ((Fin.appendEquiv _ (n B+1)).trans
            (castTraceEquiv (prefixHorizon_succ (fun b ↦ n b+1) B).symm))))

theorem executionTrace_succ (m : ℕ) (n : ℕ → ℕ) (B : ℕ)
    (h : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B)
    (y : DyadicBlockOutcome ι m (n B)) (i : Fin (prefixHorizon (fun b ↦ n b+1) (B+1))) :
    (executionTraceEquiv (ι := ι) m n (B+1) (h,y)).2 i=
      Fin.append (executionTraceEquiv (ι := ι) m n B h).2 (dyadicTraceEquiv (ι := ι) m (n B) y).2
        (Fin.cast (prefixHorizon_succ (fun b ↦ n b+1) B) i) := rfl

theorem executionTrace_eq_actions (default : ι) (m : ℕ) (n : ℕ → ℕ) (B : ℕ)
    (h : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B)
    (i : Fin (prefixHorizon (fun b ↦ n b+1) B)) :
    (executionTraceEquiv (ι := ι) m n B h).2 i=
      ScheduledExecution.trajectory default (fun b ↦ n b+1)
        (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B h i.val := by
  induction B with
  | zero => exact Fin.elim0 i
  | succ B ih =>
    rcases h with ⟨h,y⟩
    rw [executionTrace_succ]
    change Fin.append (executionTraceEquiv (ι := ι) m n B h).2 (dyadicTraceEquiv (ι := ι) m (n B) y).2
      (Fin.cast (prefixHorizon_succ (fun b ↦ n b+1) B) i)=
        Model.appendActions (prefixHorizon (fun b ↦ n b+1) B)
          (ScheduledExecution.trajectory default (fun b ↦ n b+1)
            (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B h)
          (blockActions default (Restarts.parts (n B) y.2.1) y.2.2) i.val
    by_cases ht : i.val<prefixHorizon (fun b ↦ n b+1) B
    · let j : Fin (prefixHorizon (fun b ↦ n b+1) B) := ⟨i.val,ht⟩
      have hCast : Fin.cast (prefixHorizon_succ (fun b ↦ n b+1) B) i=Fin.castAdd (n B+1) j := Fin.ext rfl
      rw [hCast,Fin.append_left,Model.appendActions,ite_eq_left ht]
      exact ih h j
    · let j : Fin (n B+1) := ⟨i.val-prefixHorizon (fun b ↦ n b+1) B,by
        have hi := i.isLt
        have hTotal := prefixHorizon_succ (fun b ↦ n b+1) B
        omega⟩
      have hCast : Fin.cast (prefixHorizon_succ (fun b ↦ n b+1) B) i=
          Fin.natAdd (prefixHorizon (fun b ↦ n b+1) B) j := by
        apply Fin.ext
        change i.val=prefixHorizon (fun b ↦ n b+1) B+(i.val-prefixHorizon (fun b ↦ n b+1) B)
        omega
      rw [hCast,Fin.append_right,Model.appendActions,ite_eq_right ht]
      exact dyadicTrace_eq_actions default m (n B) y j

end
end Tournament.Upper
