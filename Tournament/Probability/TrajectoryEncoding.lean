module

public import Tournament.Upper.BlockSwitches
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Tournament.FinitePath

variable {ι : Type*}

def trace : (n : ℕ) → History ι n → Fin (n+1) → ι
  | 0, h => fun _ ↦ h
  | n+1, (h,i) => Fin.snoc (trace n h) i

def ofTrace : (n : ℕ) → (Fin (n+1) → ι) → History ι n
  | 0, f => f 0
  | n+1, f => (ofTrace n (Fin.init f),f (Fin.last (n+1)))

theorem ofTrace_trace (n : ℕ) (h : History ι n) : ofTrace n (trace n h)=h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h,i⟩
    simp only [ofTrace,trace,Fin.init_snoc,Fin.snoc_last,ih h]

theorem trace_ofTrace (n : ℕ) (f : Fin (n+1) → ι) : trace n (ofTrace n f)=f := by
  induction n with
  | zero =>
    funext i
    have hi : i=0 := by apply Fin.ext; have := i.isLt; simp only [Fin.val_zero]; omega
    subst i
    rfl
  | succ n ih =>
    simp only [ofTrace,trace,ih]
    exact Fin.snoc_init_self f

def traceEquiv (n : ℕ) : History ι n ≃ (Fin (n+1) → ι) where
  toFun := trace n
  invFun := ofTrace n
  left_inv := ofTrace_trace n
  right_inv := trace_ofTrace n

theorem trace_eq_stateAt (n : ℕ) (h : History ι n) (i : Fin (n+1)) : trace n h i=stateAt n h i.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h,a⟩
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [trace,Fin.snoc_last,Fin.val_last]
      exact (stateAt_last (n+1) (h,a)).symm
    · simp only [trace,Fin.snoc_castSucc,Fin.val_castSucc]
      rw [stateAt_prefix n (h,a) j.val (by omega)]
      exact ih h j

end Tournament.FinitePath

namespace Tournament.Upper

variable {ι : Type*}
noncomputable section

def blockTraceEquiv : (ns : List ℕ) → BlockOutcome ι ns ≃ (Fin (Restarts.totalRounds ns) → ι)
  | [] => {
      toFun := fun _ i ↦ Fin.elim0 i
      invFun := fun _ ↦ ULift.up ()
      left_inv := fun h ↦ by rcases h with ⟨⟨⟩⟩; rfl
      right_inv := fun f ↦ by funext i; exact Fin.elim0 i }
  | n::ns => (Equiv.prodCongr (FinitePath.traceEquiv n) (blockTraceEquiv ns)).trans
      (Fin.appendEquiv (n+1) (Restarts.totalRounds ns))

theorem blockTrace_eq_actions (default : ι) (ns : List ℕ) (h : BlockOutcome ι ns)
    (i : Fin (Restarts.totalRounds ns)) : blockTraceEquiv (ι := ι) ns h i=blockActions default ns h i.val := by
  induction ns with
  | nil => exact Fin.elim0 i
  | cons n ns ih =>
    rcases h with ⟨h,rest⟩
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · change Fin.append (FinitePath.trace n h) (blockTraceEquiv (ι := ι) ns rest) (Fin.castAdd _ j)=
        Model.appendActions (n+1) (FinitePath.stateAt n h) (blockActions default ns rest) j.val
      rw [Fin.append_left,Model.appendActions,ite_eq_left j.isLt]
      exact FinitePath.trace_eq_stateAt n h j
    · change Fin.append (FinitePath.trace n h) (blockTraceEquiv (ι := ι) ns rest) (Fin.natAdd (n+1) j)=
        Model.appendActions (n+1) (FinitePath.stateAt n h) (blockActions default ns rest) (n+1+j.val)
      rw [Fin.append_right,Model.appendActions,ite_eq_right (by omega : ¬n+1+j.val<n+1),Nat.add_sub_cancel_left]
      exact ih rest j

theorem blockActions_injective (default : ι) (ns : List ℕ) (h h' : BlockOutcome ι ns)
    (hActions : ∀ t, t<Restarts.totalRounds ns → blockActions default ns h t=blockActions default ns h' t) :
    h=h' := by
  apply (blockTraceEquiv (ι := ι) ns).injective
  funext i
  rw [blockTrace_eq_actions default ns h i,blockTrace_eq_actions default ns h' i]
  exact hActions i.val i.isLt

end
end Tournament.Upper
