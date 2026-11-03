module

public import Tournament.Probability.TrajectoryEncoding
public import Tournament.Upper.EstimatorDyadicTail

@[expose] public section

namespace Tournament.Upper

variable {ι : Type*}
noncomputable section

def castTraceEquiv {a b : ℕ} (h : a=b) : (Fin a → ι) ≃ (Fin b → ι) where
  toFun f i := f (Fin.cast h.symm i)
  invFun f i := f (Fin.cast h i)
  left_inv := by cases h; intro f; rfl
  right_inv := by cases h; intro f; rfl

def partitionTraceEquiv (n : ℕ) (coins : Restarts.Coins n) :
    BlockOutcome ι (Restarts.parts n coins) ≃ (Fin (n+1) → ι) :=
  (blockTraceEquiv (ι := ι) (Restarts.parts n coins)).trans (castTraceEquiv (Restarts.parts_totalRounds n coins))

theorem partitionTrace_eq_actions (default : ι) (n : ℕ) (coins : Restarts.Coins n)
    (h : BlockOutcome ι (Restarts.parts n coins)) (i : Fin (n+1)) :
    partitionTraceEquiv (ι := ι) n coins h i=blockActions default (Restarts.parts n coins) h i.val := by
  change blockTraceEquiv (ι := ι) (Restarts.parts n coins) h (Fin.cast (Restarts.parts_totalRounds n coins).symm i)=_
  rw [blockTrace_eq_actions default]
  rfl

def dyadicTraceEquiv (m n : ℕ) : DyadicBlockOutcome ι m n ≃
    ((Fin (m+1) × Restarts.Coins n) × (Fin (n+1) → ι)) where
  toFun y := ((y.1,y.2.1),partitionTraceEquiv (ι := ι) n y.2.1 y.2.2)
  invFun q := ⟨q.1.1,q.1.2,(partitionTraceEquiv (ι := ι) n q.1.2).symm q.2⟩
  left_inv := by
    rintro ⟨j,coins,h⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨j,coins⟩,f⟩
    simp only [Equiv.apply_symm_apply]

theorem dyadicTrace_eq_actions (default : ι) (m n : ℕ) (y : DyadicBlockOutcome ι m n) (i : Fin (n+1)) :
    (dyadicTraceEquiv (ι := ι) m n y).2 i=blockActions default (Restarts.parts n y.2.1) y.2.2 i.val :=
  partitionTrace_eq_actions default n y.2.1 y.2.2 i

theorem dyadicOutcome_eq_of_metadata_actions (default : ι) (m n : ℕ) (y z : DyadicBlockOutcome ι m n)
    (hRate : y.1=z.1) (hCoins : y.2.1=z.2.1)
    (hActions : ∀ t, t<n+1 →
      blockActions default (Restarts.parts n y.2.1) y.2.2 t=
        blockActions default (Restarts.parts n z.2.1) z.2.2 t) : y=z := by
  apply (dyadicTraceEquiv (ι := ι) m n).injective
  apply Prod.ext
  · exact Prod.ext hRate hCoins
  · funext i
    rw [dyadicTrace_eq_actions default,dyadicTrace_eq_actions default]
    exact hActions i.val i.isLt

end
end Tournament.Upper
