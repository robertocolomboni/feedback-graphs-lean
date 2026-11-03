module

public import Tournament.Computation.FiniteRequests

@[expose] public section

namespace Tournament.Computation.FiniteChunkRunner

open Model FiniteRequests

variable {K : ℕ}

abbrev Prefix (K n : ℕ) := FinitePath.History (Fin K) n × ComparisonHistory (Fin K) n
abbrev Result (K n : ℕ) := FinitePath.History (Fin K) n ×
  (ComparisonHistory (Fin K) n × (Fin K → ℝ))

noncomputable def runPrefix (policy : GraphPolicy (Fin K)) (offset : ℕ) :
    (n : ℕ) → Program K (Prefix K n)
  | 0 => (Program.sample policy.initial).map (fun i => (i,i))
  | n+1 => (runPrefix policy offset n).bind fun past =>
      (Program.observation (offset+n) (currentAction n past.2)).bind fun obs =>
        (Program.sample (policy.next n past.2 obs)).map fun i =>
          ((past.1,i),((past.2,obs),i))

noncomputable def execute (policy : GraphPolicy (Fin K)) (offset n : ℕ) :
    Program K (Result K n) :=
  (runPrefix policy offset n).bind fun past =>
    (Program.observation (offset+n) (currentAction n past.2)).map fun obs =>
      (past.1,(past.2,obs))

noncomputable def observations (E : Fin K → Fin K → Prop) (loss : ℕ → Fin K → ℝ) :
    ℕ → Fin K → Fin K → ℝ := fun t i => graphObservation E i (loss t)

theorem prefix_expect (policy : GraphPolicy (Fin K)) (E : Fin K → Fin K → Prop)
    (loss : ℕ → Fin K → ℝ) (offset n : ℕ) (f : Prefix K n → ℝ) :
    Program.expect (observations E loss) (runPrefix policy offset n) f =
      (policy.law E (fun t => loss (offset+t)) n).mean
        (fun h => f (h, recordGraph E (fun t => loss (offset+t)) n h)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [runPrefix, Program.expect_bind, Program.expect_map, Program.expect_sample,
        Program.expect_observation]
      rw [ih]
      rw [GraphPolicy.law, ProbabilityVector.joint_mean]
      congr 1
      funext h
      simp only [recordGraph_current, observations, recordGraph]

theorem execute_expect (policy : GraphPolicy (Fin K)) (E : Fin K → Fin K → Prop)
    (loss : ℕ → Fin K → ℝ) (offset n : ℕ) (f : Result K n → ℝ) :
    Program.expect (observations E loss) (execute policy offset n) f =
      (policy.law E (fun t => loss (offset+t)) n).mean
        (fun h => f (h,(recordGraph E (fun t => loss (offset+t)) n h,
          graphObservation E (FinitePath.lastState n h) (loss (offset+n))))) := by
  simp only [execute, Program.expect_bind, Program.expect_map, Program.expect_observation]
  rw [prefix_expect]
  congr 1
  funext h
  simp only [recordGraph_current, observations]

end Tournament.Computation.FiniteChunkRunner
