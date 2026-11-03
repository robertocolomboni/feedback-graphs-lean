module

public import Tournament.Upper.GeometricAccounting
public import Tournament.Model.Regret

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open scoped Classical BigOperators
noncomputable section

def arm (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) : Bool :=
  (roundStart (state d coins t) t (coins t)).isSome

theorem starts_of_rise (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ)
    (hPrev : arm d coins t=false) (hNext : arm d coins (t+1)=true) : Starts d coins (t+1) := by
  have hNone : roundStart (state d coins t) t (coins t)=none := by
    cases hr : roundStart (state d coins t) t (coins t) with
    | none => rfl
    | some a => simp [arm,hr] at hPrev
  have hState : (state d coins (t+1)).start=none := by simp [state,advance,hNone,resting]
  refine ⟨hState,?_⟩
  cases hc : coins (t+1) with
  | false => simp [arm,roundStart,hState,hc] at hNext
  | true => rfl

theorem switches_succ_succ (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    Model.switchCount (n+2) (arm d coins)=Model.switchCount (n+1) (arm d coins)+
      (if arm d coins (n+1)=arm d coins n then 0 else 1) := by
  change (∑ t∈Finset.range (n+1), if arm d coins (t+1)=arm d coins t then 0 else 1)=
    (∑ t∈Finset.range n, if arm d coins (t+1)=arm d coins t then 0 else 1)+_
  exact Finset.sum_range_succ _ n

theorem switches_with_final_bonus (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    Model.switchCount (n+1) (arm d coins)+(if arm d coins n=true then 1 else 0)≤
      2*probeCount d coins (n+1) := by
  induction n with
  | zero =>
    cases hc : coins 0 <;>
      simp [arm,state,Starts,probeCount,roundStart,resting,hc,Model.switchCount]
  | succ n ih =>
    have hCount : probeCount d coins (n+2)=probeCount d coins (n+1)+
        (if Starts d coins (n+1) then 1 else 0) := by rw [probeCount,Finset.sum_range_succ]; rfl
    rw [switches_succ_succ,hCount]
    cases hp : arm d coins n with
    | false =>
      cases hn : arm d coins (n+1) with
      | false =>
        simp [hp] at ih ⊢
        split_ifs <;> omega
      | true =>
        have hStart := starts_of_rise d coins n hp hn
        simp [hp,hStart] at ih ⊢
        omega
    | true =>
      cases hn : arm d coins (n+1) with
      | false =>
        simp [hp] at ih ⊢
        split_ifs <;> omega
      | true =>
        simp [hp] at ih ⊢
        split_ifs <;> omega

theorem switches_le_twice_probes (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    Model.switchCount T (arm d coins)≤2*probeCount d coins T := by
  cases T with
  | zero => simp [Model.switchCount,probeCount]
  | succ n => have h := switches_with_final_bonus d coins n; split_ifs at h <;> omega

theorem blind_comparison_le (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) (hd : ∀ t<T, d t≤1) :
    playedGain d coins T+(Model.switchCount T (arm d coins):ℝ)≤3*(probeCount d coins T:ℝ) := by
  have hGain := playedGain_le_probes d coins T hd
  have hSwitch : (Model.switchCount T (arm d coins):ℝ)≤2*(probeCount d coins T:ℝ) := by
    exact_mod_cast switches_le_twice_probes d coins T
  linarith

theorem revealing_comparison_le (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ)
    (hd : ∀ t<T, -1≤d t ∧ d t≤1) :
    playedGain d coins T-cumulative d T+(Model.switchCount T (arm d coins):ℝ)≤
      (terminalCount d T (finalStart d coins T):ℝ)+3*(probeCount d coins T:ℝ) := by
  have hMiss := missed_advantage_pathwise d coins T hd
  have hPartition := cumulative_eq_played_add_resting d coins T
  have hSwitch : (Model.switchCount T (arm d coins):ℝ)≤2*(probeCount d coins T:ℝ) := by
    exact_mod_cast switches_le_twice_probes d coins T
  linarith

end
end Tournament.Upper.GeometricProbing
