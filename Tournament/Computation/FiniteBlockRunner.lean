module

public import Tournament.Computation.FiniteChunkRunner

@[expose] public section

namespace Tournament.Computation.FiniteBlockRunner

open Model Upper FiniteRequests FiniteChunkRunner

variable {K : ℕ}

abbrev ResetResult (K : ℕ) (ns : List ℕ) := BlockOutcome (Fin K) ns × BlockTranscript (Fin K) ns

noncomputable def reset (policy : GraphResetPolicy (Fin K)) :
    (offset : ℕ) → (ns : List ℕ) → Program K (ResetResult K ns)
  | _, [] => .pure (ULift.up (),ULift.up ())
  | offset, n::ns => (FiniteChunkRunner.execute (policy.chunk offset n) offset n).bind fun first =>
      (reset policy (offset+(n+1)) ns).map fun rest =>
        ((first.1,rest.1),(first.2,rest.2))

theorem reset_expect (policy : GraphResetPolicy (Fin K)) (E : Fin K → Fin K → Prop)
    (loss : ℕ → Fin K → ℝ) (ns : List ℕ) : ∀ offset (f : ResetResult K ns → ℝ),
    Program.expect (observations E loss) (reset policy offset ns) f =
      (policy.law E loss offset ns).mean (fun h => f (h, recordBlockGraph E loss offset ns h)) := by
  induction ns with
  | nil =>
      intro offset f
      simp [reset, GraphResetPolicy.law, recordBlockGraph, ProbabilityVector.mean, ProbabilityVector.pure]
  | cons n ns ih =>
      intro offset f
      simp only [reset, Program.expect_bind, Program.expect_map]
      rw [execute_expect]
      change _ = ((_ : ProbabilityVector (FinitePath.History (Fin K) n)).joint
        (fun _ => policy.law E loss (offset+(n+1)) ns)).mean _
      rw [ProbabilityVector.joint_mean]
      congr 1
      funext h
      rw [ih]
      rfl

noncomputable def coins (τ : ℝ) (hτ : 0≤τ) (hτ1 : τ≤1) :
    (n : ℕ) → Program K (Restarts.Coins n)
  | 0 => .pure ()
  | n+1 => (Program.sample (Restarts.coin τ hτ hτ1)).bind fun b =>
      (coins τ hτ hτ1 n).map fun tail => (b,tail)

theorem coins_expect (τ : ℝ) (hτ : 0≤τ) (hτ1 : τ≤1)
    (obs : ℕ → Fin K → Fin K → ℝ) (n : ℕ) (f : Restarts.Coins n → ℝ) :
    Program.expect obs (coins τ hτ hτ1 n) f = (Restarts.law τ hτ hτ1 n).mean f := by
  induction n with
  | zero => simp [coins, Program.expect_pure, Restarts.law, ProbabilityVector.mean]
  | succ n ih =>
      simp only [coins, Program.expect_bind, Program.expect_sample, Program.expect_map]
      rw [Restarts.law, ProbabilityVector.joint_mean]
      congr 1
      funext b
      exact ih _

abbrev Result (K m n : ℕ) := (y : DyadicBlockOutcome (Fin K) m n) ×
  BlockTranscript (Fin K) (Restarts.parts n y.2.1)

noncomputable def execute {m : ℕ} (policy : GraphRestartPolicy (Fin K) m) (offset n : ℕ) :
    Program K (Result K m n) :=
  (Program.sample policy.rates).bind fun j =>
    (coins (policy.restart j) (policy.restart_nonneg j) (policy.restart_le_one j) n).bind fun c =>
      (reset (policy.chunks j) offset (Restarts.parts n c)).map fun out =>
        ⟨⟨j,⟨c,out.1⟩⟩,out.2⟩

theorem execute_expect {m : ℕ} (policy : GraphRestartPolicy (Fin K) m)
    (E : Fin K → Fin K → Prop) (loss : ℕ → Fin K → ℝ) (offset n : ℕ)
    (f : Result K m n → ℝ) :
    Program.expect (observations E loss) (execute policy offset n) f =
      (policy.law E loss offset n).mean
        (fun y => f ⟨y,recordBlockGraph E loss offset (Restarts.parts n y.2.1) y.2.2⟩) := by
  simp only [execute, Program.expect_bind, Program.expect_sample, Program.expect_map]
  rw [GraphRestartPolicy.law, ProbabilityVector.sigmaJoint_mean]
  congr 1
  funext j
  rw [coins_expect, ProbabilityVector.sigmaJoint_mean]
  congr 1
  funext c
  rw [reset_expect]

end Tournament.Computation.FiniteBlockRunner
