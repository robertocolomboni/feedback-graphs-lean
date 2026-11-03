module

public import Tournament.Computation.FiniteTournamentProgram

@[expose] public section

namespace Tournament.Computation.FiniteProgramHorizon

open Model Upper FiniteRequests FiniteChunkRunner FiniteTournamentProgram
open scoped BigOperators

variable {K : ℕ} {α β : Type}

def Observes : Program K α → List ℕ → Prop
  | .pure _, times => times=[]
  | @Program.draw _ _ _γ _inst _ next, times => ∀ x, Observes (next x) times
  | .observe time _ next, times =>
      ∃ rest, times=time::rest ∧ ∀ obs, Observes (next obs) rest

theorem observes_bind (p : Program K α) (next : α → Program K β)
    (times more : List ℕ) (hp : Observes p times)
    (hn : ∀ x, Observes (next x) more) :
    Observes (p.bind next) (times++more) := by
  induction p generalizing times with
  | pure x =>
      change times=[] at hp
      subst times
      exact hn x
  | draw law cont ih =>
      intro x
      exact ih x times (hp x)
  | observe time action cont ih =>
      obtain ⟨rest, rfl, hr⟩ := hp
      exact ⟨rest++more,rfl,fun obs => ih obs rest (hr obs)⟩

theorem observes_map (p : Program K α) (f : α → β) (times : List ℕ)
    (hp : Observes p times) : Observes (p.map f) times := by
  simpa only [Program.map, List.append_nil] using observes_bind p (fun x => .pure (f x)) times [] hp
    (fun _ => rfl)

theorem observes_sample {γ : Type} [Fintype γ] (p : ProbabilityVector γ) :
    Observes (Program.sample (K:=K) p) [] := fun _ => rfl

theorem observes_observation (time : ℕ) (action : Fin K) :
    Observes (Program.observation time action) [time] := ⟨[],rfl,fun _ => rfl⟩

theorem prefix_observes (policy : GraphPolicy (Fin K)) (offset n : ℕ) :
    Observes (runPrefix policy offset n) (List.range' offset n) := by
  induction n with
  | zero => exact observes_map _ _ [] (observes_sample _)
  | succ n ih =>
      rw [runPrefix, List.range'_1_concat]
      apply observes_bind _ _ _ _ ih
      intro past
      apply observes_bind _ _ [offset+n] [] (observes_observation _ _)
      intro obs
      exact observes_map _ _ [] (observes_sample _)

theorem chunk_observes (policy : GraphPolicy (Fin K)) (offset n : ℕ) :
    Observes (FiniteChunkRunner.execute policy offset n) (List.range' offset (n+1)) := by
  rw [FiniteChunkRunner.execute, List.range'_1_concat]
  apply observes_bind _ _ _ _ (prefix_observes policy offset n)
  intro past
  exact observes_map _ _ [offset+n] (observes_observation _ _)

theorem reset_observes (policy : GraphResetPolicy (Fin K)) (ns : List ℕ) :
    ∀ offset, Observes (FiniteBlockRunner.reset policy offset ns)
      (List.range' offset (Restarts.totalRounds ns)) := by
  induction ns with
  | nil => intro offset; rfl
  | cons n ns ih =>
      intro offset
      rw [Restarts.totalRounds, ← List.range'_append_1, FiniteBlockRunner.reset]
      apply observes_bind _ _ _ _ (chunk_observes _ _ _)
      intro first
      exact observes_map _ _ _ (ih _)

theorem coins_observes (τ : ℝ) (hτ : 0≤τ) (hτ1 : τ≤1) (n : ℕ) :
    Observes (FiniteBlockRunner.coins (K:=K) τ hτ hτ1 n) [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact observes_bind _ _ [] [] (observes_sample _)
        (fun _ => observes_map _ _ [] ih)

theorem block_observes {m : ℕ} (policy : GraphRestartPolicy (Fin K) m) (offset n : ℕ) :
    Observes (FiniteBlockRunner.execute policy offset n) (List.range' offset (n+1)) := by
  apply observes_bind _ _ [] _ (observes_sample _)
  intro j
  apply observes_bind _ _ [] _ (coins_observes _ _ _ _)
  intro c
  apply observes_map
  simpa only [Restarts.parts_totalRounds, List.range'_succ] using
    reset_observes (policy.chunks j) (Restarts.parts n c) offset

theorem adaptive_observes [Nonempty (Fin K)] {m : ℕ}
    (policy : GraphFeedbackEW (Fin K) m) (n : ℕ → ℕ) (B : ℕ) :
    Observes (FiniteAdaptiveRunner.execute policy n B)
      (List.range' 0 (prefixHorizon (fun b => n b+1) B)) := by
  induction B with
  | zero => rfl
  | succ B ih =>
      rw [prefixHorizon_succ, ← List.range'_append_1, Nat.zero_add,
        FiniteAdaptiveRunner.execute]
      apply observes_bind _ _ _ _ ih
      intro past
      exact observes_map _ _ _ (block_observes _ _ _)

theorem constant_observes (default : Fin K) (T : ℕ) :
    Observes (constantProgram default T) (List.range T) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [constantProgram, List.range_succ]
      apply observes_bind _ _ _ _ ih
      intro past
      exact observes_map _ _ [T] (observes_observation _ _)

theorem schedule_horizon (S : SteeringParameters (Fin K)) :
    prefixHorizon (fun b => S.schedule b+1) S.blockCount = S.T :=
  UniformSchedule.total S.T (BlockParameters.horizon S.m)
    (by unfold BlockParameters.horizon; positivity)

theorem optimizer_observes [Nonempty (Fin K)] (S : SteeringParameters (Fin K))
    (E : Fin K → Fin K → Prop) :
    Observes (FiniteAdaptiveRunner.optimizerProgram S E S.schedule S.blockCount) (List.range S.T) := by
  simpa only [FiniteAdaptiveRunner.optimizerProgram, schedule_horizon, List.range_eq_range'] using
    adaptive_observes ((PreparedPolicy.feedbackPolicy S).toGraph E) S.schedule S.blockCount

theorem tournamentProgram_observes [Nonempty (Fin K)]
    (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E) (T : ℕ) (default : Fin K) :
    Observes (tournamentProgram E hE T default) (List.range T) := by
  unfold tournamentProgram
  split
  · exact constant_observes default T
  · split
    · split
      · exact observes_map _ _ _ (optimizer_observes _ E)
      · exact constant_observes default T
    · exact constant_observes default T

theorem preparation_count_le [Nonempty (Fin K)] (S : SteeringParameters (Fin K)) :
    S.blockCount≤S.T := by
  rw [← schedule_horizon S]
  unfold prefixHorizon
  calc
    S.blockCount = ∑ _b ∈ Finset.range S.blockCount, 1 := by simp
    _ ≤ ∑ b ∈ Finset.range S.blockCount, (S.schedule b+1) :=
      Finset.sum_le_sum (fun _ _ => Nat.le_add_left 1 _)

end Tournament.Computation.FiniteProgramHorizon
