module

public import Tournament.Upper.GeometricFinalProbe

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open scoped Classical BigOperators
noncomputable section

def Closes (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) : Prop :=
  Playing d coins t ∧ ¬((state d coins t).balance+d t<0)

def probeCount (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℕ :=
  ∑ t∈Finset.range T, if Starts d coins t then 1 else 0

def completionCount (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℕ :=
  ∑ t∈Finset.range T, if Closes d coins t then 1 else 0

def closedGain (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℝ :=
  ∑ t∈Finset.range T, if Closes d coins t then (state d coins t).balance+d t else 0

def playedGain (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℝ :=
  ∑ t∈Finset.range T, if Playing d coins t then d t else 0

def restingGain (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℝ :=
  ∑ t∈Finset.range T, if Playing d coins t then 0 else d t

def activeFlag (q : ProbeState) : ℕ := if q.start=none then 0 else 1

theorem probeCount_eq_card (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    probeCount d coins T=((Finset.range T).filter (Starts d coins)).card := by
  simp only [probeCount,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem completionCount_eq_card (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    completionCount d coins T=((Finset.range T).filter (Closes d coins)).card := by
  simp only [completionCount,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem probeCount_mono (d : ℕ → ℝ) (coins : ℕ → Bool) {s T : ℕ} (hs : s≤T) :
    probeCount d coins s≤probeCount d coins T := by
  rw [probeCount_eq_card,probeCount_eq_card]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hs))

theorem count_step (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    (if Starts d coins n then 1 else 0)+activeFlag (state d coins n)=
      (if Closes d coins n then 1 else 0)+activeFlag (state d coins (n+1)) := by
  cases hStart : (state d coins n).start with
  | none =>
    cases hc : coins n <;> by_cases hb : (state d coins n).balance+d n<0 <;>
      simp [Starts,Closes,Playing,activeFlag,state,advance,roundStart,hStart,hc,hb,resting]
  | some a =>
    by_cases hb : (state d coins n).balance+d n<0 <;>
      simp [Starts,Closes,Playing,activeFlag,state,advance,roundStart,hStart,hb,resting]

theorem starts_eq_completions_add_active (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    probeCount d coins T=completionCount d coins T+activeFlag (state d coins T) := by
  induction T with
  | zero => simp [probeCount,completionCount,state,activeFlag,resting]
  | succ T ih =>
    have hStep := count_step d coins T
    simp only [probeCount,completionCount,Finset.sum_range_succ] at ih ⊢
    omega

theorem completionCount_le_probes (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    completionCount d coins T≤probeCount d coins T := by
  rw [starts_eq_completions_add_active]
  omega

theorem gain_step (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    (if Playing d coins n then d n else 0)=
      (if Closes d coins n then (state d coins n).balance+d n else 0)+
        (state d coins (n+1)).balance-(state d coins n).balance := by
  cases hr : roundStart (state d coins n) n (coins n) with
  | none =>
    have hNone := (roundStart_none_iff (state d coins n) n (coins n)).mp hr
    have hBalance := state_none_balance d coins n hNone.1
    simp [Playing,Closes,hr,state,advance,resting,hBalance]
  | some a =>
    by_cases hb : (state d coins n).balance+d n<0 <;>
      simp [Playing,Closes,hr,state,advance,hb,resting]

theorem playedGain_eq_closed_add_balance (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    playedGain d coins T=closedGain d coins T+(state d coins T).balance := by
  induction T with
  | zero => simp [playedGain,closedGain,state,resting]
  | succ T ih =>
    have hStep := gain_step d coins T
    simp only [playedGain,closedGain,Finset.sum_range_succ] at ih ⊢
    linarith

theorem closedGain_le_completions (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ)
    (hd : ∀ t<T, d t≤1) : closedGain d coins T≤(completionCount d coins T:ℝ) := by
  have hCast : (completionCount d coins T:ℝ)=∑ t∈Finset.range T, if Closes d coins t then (1:ℝ) else 0 := by
    simp only [completionCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hCast]
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : Closes d coins t
  · rw [ite_eq_left h,ite_eq_left h]
    have hState := state_balance_nonpos d coins t
    have hD := hd t (Finset.mem_range.mp ht)
    linarith
  · rw [ite_eq_right h,ite_eq_right h]

theorem closed_probe_balance (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) (h : Closes d coins t)
    (hd : d t≤1) : 0≤(state d coins t).balance+d t ∧ (state d coins t).balance+d t≤1 := by
  have hState := state_balance_nonpos d coins t
  exact ⟨le_of_not_gt h.2,by linarith⟩

theorem round_balance_identity (d : ℕ → ℝ) (coins : ℕ → Bool) (t a : ℕ)
    (hRound : roundStart (state d coins t) t (coins t)=some a) :
    (state d coins t).balance+d t=cumulative d (t+1)-cumulative d a := by
  rcases (roundStart_eq_some_iff (state d coins t) t a (coins t)).mp hRound with hOld | ⟨hNone,_,ha⟩
  · rw [(active_origin d coins t a hOld).2.2.1,prefix_succ]
    ring
  · subst a
    rw [state_none_balance d coins t hNone,prefix_succ]
    ring

theorem completed_probe_interval (d : ℕ → ℝ) (coins : ℕ → Bool) (t a : ℕ)
    (hRound : roundStart (state d coins t) t (coins t)=some a) (hClose : Closes d coins t)
    (hd : d t≤1) :
    a≤t ∧ Starts d coins a ∧
      (∀ u, a<u → u≤t → cumulative d u<cumulative d a) ∧
      (∀ u, a≤u → u≤t → roundStart (state d coins u) u (coins u)=some a) ∧
      (0≤cumulative d (t+1)-cumulative d a ∧ cumulative d (t+1)-cumulative d a≤1) := by
  obtain ⟨ha,hStart,hPast,hInterval⟩ := roundStart_origin d coins t a hRound
  have hBalance := closed_probe_balance d coins t hClose hd
  rw [round_balance_identity d coins t a hRound] at hBalance
  exact ⟨ha,hStart,hPast,hInterval,hBalance⟩

theorem no_terminal_in_completed_probe (d : ℕ → ℝ) (coins : ℕ → Bool) (T t a : ℕ)
    (ht : t<T) (hRound : roundStart (state d coins t) t (coins t)=some a) (hClose : Closes d coins t)
    (u : ℕ) (hau : a≤u) (hut : u≤t) : ¬Terminal d T u := by
  obtain ⟨_,_,hPast,_⟩ := roundStart_origin d coins t a hRound
  have hEnd : cumulative d a≤cumulative d (t+1) := by
    have hBalance := le_of_not_gt hClose.2
    rw [round_balance_identity d coins t a hRound] at hBalance
    linarith
  have hU : cumulative d u≤cumulative d a := by
    by_cases hEq : u=a
    · simp only [hEq,le_rfl]
    · exact (hPast u (by omega) hut).le
  intro hTerm
  have hFuture := (terminal_iff d T u (by omega)).mp hTerm (t+1) (by omega) (by omega)
  linarith

theorem playedGain_le_probes (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ)
    (hd : ∀ t<T, d t≤1) : playedGain d coins T≤(probeCount d coins T:ℝ) := by
  rw [playedGain_eq_closed_add_balance]
  have hGain := closedGain_le_completions d coins T hd
  have hBalance := state_balance_nonpos d coins T
  have hCount : (completionCount d coins T:ℝ)≤(probeCount d coins T:ℝ) := by
    exact_mod_cast completionCount_le_probes d coins T
  linarith

theorem cumulative_eq_played_add_resting (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    cumulative d T=playedGain d coins T+restingGain d coins T := by
  rw [cumulative,playedGain,restingGain,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : Playing d coins t <;> simp [h]

theorem restingGain_eq_before_finalStart (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    restingGain d coins T=restingGain d coins (finalStart d coins T) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (finalStart_le_horizon d coins T))
  intro t ht hBefore
  have hLower : finalStart d coins T≤t := by
    have hn : ¬t<finalStart d coins T := fun h ↦ hBefore (Finset.mem_range.mpr h)
    omega
  exact ite_eq_left (playing_after_finalStart d coins T t hLower (Finset.mem_range.mp ht))

theorem missed_advantage_pathwise (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ)
    (hd : ∀ t<T, -1≤d t ∧ d t≤1) :
    -restingGain d coins T≤(terminalCount d T (finalStart d coins T):ℝ)+(probeCount d coins T:ℝ) := by
  have hs := finalStart_le_horizon d coins T
  have hPrefix := negative_prefix_le_terminal_count d T _ hs (fun t ht ↦ (hd t ht).1) (finalStart_boundary d coins T)
  have hPlayed := playedGain_le_probes d coins (finalStart d coins T) (fun t ht ↦ (hd t (by omega)).2)
  have hCount : (probeCount d coins (finalStart d coins T):ℝ)≤(probeCount d coins T:ℝ) := by
    exact_mod_cast probeCount_mono d coins hs
  have hPartition := cumulative_eq_played_add_resting d coins (finalStart d coins T)
  rw [restingGain_eq_before_finalStart]
  linarith

end
end Tournament.Upper.GeometricProbing
