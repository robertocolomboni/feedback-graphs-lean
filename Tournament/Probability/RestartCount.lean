module

public import Tournament.Probability.ChunkPartitions
public import Tournament.Probability.StoppedChunkCoupling

@[expose] public section

namespace Tournament.Restarts

open scoped Classical

noncomputable section

def restartCount : (n : ℕ) → Coins n → ℕ
  | 0, _ => 0
  | n+1, (stop,rest) => (if stop then 1 else 0)+restartCount n rest

theorem parts_boundary_count (n : ℕ) (coins : Coins n) : (parts n coins).length-1 = restartCount n coins := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases coins with ⟨stop,rest⟩
    have h := ih rest
    cases stop <;> simp only [parts,plan,Bool.false_eq_true,ite_false,ite_true,
      List.length_cons,restartCount] at h ⊢ <;> omega

theorem expected_restartCount {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (law τ hτ hτ1 n).mean (fun coins ↦ (restartCount n coins : ℝ)) = (n:ℝ)*τ := by
  induction n with
  | zero =>
    have heq : (fun coins : Coins 0 ↦ (restartCount 0 coins : ℝ)) = (fun _ ↦ 0) := by
      funext coins
      simp [restartCount]
    rw [heq,ProbabilityVector.mean_const]
    simp
  | succ n ih =>
    change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
      (fun pair : Bool × Coins n ↦ (restartCount (n+1) pair : ℝ)) = _
    rw [ProbabilityVector.joint_mean,coin_mean]
    have htrue : (fun rest : Coins n ↦ (restartCount (n+1) (true,rest) : ℝ)) =
        (fun rest ↦ 1+(restartCount n rest : ℝ)) := by
      funext rest
      simp [restartCount]
    have hfalse : (fun rest : Coins n ↦ (restartCount (n+1) (false,rest) : ℝ)) =
        (fun rest ↦ (restartCount n rest : ℝ)) := by
      funext rest
      simp [restartCount]
    rw [htrue,hfalse,ProbabilityVector.mean_add,ProbabilityVector.mean_const,ih]
    push_cast
    ring

end
end Tournament.Restarts
