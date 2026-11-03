module

public import Tournament.Upper.GeometricExecution
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open scoped Classical
noncomputable section

def terminalSuccesses (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t ↦ Terminal d T t ∧ coins t=true)

def finalStart (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : ℕ :=
  if h : (terminalSuccesses d coins T).Nonempty then (terminalSuccesses d coins T).min' h else T

theorem finalStart_le_horizon (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) : finalStart d coins T≤T := by
  unfold finalStart
  split_ifs with h
  · have hm := Finset.min'_mem (terminalSuccesses d coins T) h
    exact (Finset.mem_range.mp (Finset.mem_filter.mp hm).1).le
  · exact le_rfl

theorem finalStart_le_of_success (d : ℕ → ℝ) (coins : ℕ → Bool) (T t : ℕ)
    (ht : t<T) (hTerm : Terminal d T t) (hCoin : coins t=true) : finalStart d coins T≤t := by
  have hm : t∈terminalSuccesses d coins T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,hTerm,hCoin⟩
  have hNon : (terminalSuccesses d coins T).Nonempty := ⟨t,hm⟩
  rw [finalStart,dite_eq_left hNon]
  exact Finset.min'_le _ t hm

theorem finalStart_success (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) (h : finalStart d coins T<T) :
    Terminal d T (finalStart d coins T) ∧ coins (finalStart d coins T)=true := by
  unfold finalStart at h ⊢
  split_ifs with hNon
  · exact (Finset.mem_filter.mp (Finset.min'_mem (terminalSuccesses d coins T) hNon)).2
  · simp only [dite_eq_right hNon] at h
    omega

theorem terminal_coin_before_finalStart (d : ℕ → ℝ) (coins : ℕ → Bool) (T t : ℕ)
    (ht : t<finalStart d coins T) (hTerm : Terminal d T t) : coins t=false := by
  have hT := finalStart_le_horizon d coins T
  cases hc : coins t with
  | false => rfl
  | true => have := finalStart_le_of_success d coins T t (by omega) hTerm hc; omega

theorem active_terminal_origin (d : ℕ → ℝ) (coins : ℕ → Bool) (T t a : ℕ)
    (ht : t<T) (hActive : (state d coins t).start=some a) (hTerm : Terminal d T t) :
    Terminal d T a ∧ Starts d coins a := by
  obtain ⟨ha,hStart,_,hPast⟩ := active_origin d coins t a hActive
  refine ⟨(terminal_iff d T a (by omega)).mpr ?_,hStart⟩
  intro u hau huT
  by_cases hu : u≤t
  · exact hPast u hau hu
  · have hFuture := (terminal_iff d T t ht).mp hTerm u (by omega) huT
    exact hFuture.trans (hPast t ha le_rfl)

theorem resting_at_terminal_before_boundary (d : ℕ → ℝ) (coins : ℕ → Bool) (T t : ℕ)
    (ht : t<T) (hBefore : t≤finalStart d coins T) (hTerm : Terminal d T t) :
    (state d coins t).start=none := by
  cases ha : (state d coins t).start with
  | none => rfl
  | some a =>
    obtain ⟨hTermA,hStartA⟩ := active_terminal_origin d coins T t a ht ha hTerm
    have haT := (active_origin d coins t a ha).1
    have hMin := finalStart_le_of_success d coins T a (by omega) hTermA hStartA.2
    omega

theorem finalStart_starts (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) (h : finalStart d coins T<T) :
    Starts d coins (finalStart d coins T) := by
  have hSuccess := finalStart_success d coins T h
  exact ⟨resting_at_terminal_before_boundary d coins T _ h le_rfl hSuccess.1,hSuccess.2⟩

theorem terminal_probe_continues (d : ℕ → ℝ) (coins : ℕ → Bool) (T s : ℕ)
    (hs : s<T) (hStart : Starts d coins s) (hTerm : Terminal d T s) :
    ∀ n, s<n → n≤T → (state d coins n).start=some s := by
  have hBase : (state d coins (s+1)).start=some s := by
    apply (state_succ_active_iff d coins s s).mpr
    constructor
    · exact (roundStart_eq_some_iff (state d coins s) s s (coins s)).mpr (Or.inr ⟨hStart.1,hStart.2,rfl⟩)
    · rw [state_none_balance d coins s hStart.1,zero_add]
      have h := (terminal_iff d T s hs).mp hTerm (s+1) (by omega) (by omega)
      rw [prefix_succ] at h
      linarith
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hsn hnT
    by_cases hEq : n=s
    · simpa only [hEq] using hBase
    · have hns : s<n := by omega
      have hOld := ih hns (by omega)
      apply (state_succ_active_iff d coins n s).mpr
      constructor
      · exact (roundStart_eq_some_iff (state d coins n) n s (coins n)).mpr (Or.inl hOld)
      · have hBalance := (active_origin d coins n s hOld).2.2.1
        rw [hBalance]
        have hFuture := (terminal_iff d T s hs).mp hTerm (n+1) (by omega) hnT
        rw [prefix_succ] at hFuture
        linarith

theorem playing_of_starts (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) (h : Starts d coins t) :
    Playing d coins t := by
  have hr := (roundStart_eq_some_iff (state d coins t) t t (coins t)).mpr (Or.inr ⟨h.1,h.2,rfl⟩)
  unfold Playing
  rw [hr]
  rfl

theorem playing_of_active (d : ℕ → ℝ) (coins : ℕ → Bool) (t a : ℕ)
    (h : (state d coins t).start=some a) : Playing d coins t := by
  have hr := (roundStart_eq_some_iff (state d coins t) t a (coins t)).mpr (Or.inl h)
  unfold Playing
  rw [hr]
  rfl

theorem playing_after_finalStart (d : ℕ → ℝ) (coins : ℕ → Bool) (T t : ℕ)
    (hBefore : finalStart d coins T≤t) (ht : t<T) : Playing d coins t := by
  have hs : finalStart d coins T<T := by omega
  have hStart := finalStart_starts d coins T hs
  by_cases hEq : t=finalStart d coins T
  · simpa only [hEq] using playing_of_starts d coins _ hStart
  · have hActive := terminal_probe_continues d coins T _ hs hStart (finalStart_success d coins T hs).1 t (by omega) ht.le
    exact playing_of_active d coins t _ hActive

theorem state_finalStart_none (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    (state d coins (finalStart d coins T)).start=none := by
  have hsT := finalStart_le_horizon d coins T
  by_cases hs : finalStart d coins T<T
  · exact (finalStart_starts d coins T hs).1
  · have hEq : finalStart d coins T=T := by omega
    rw [hEq]
    cases ha : (state d coins T).start with
    | none => rfl
    | some a =>
      obtain ⟨haT,hStart,_,hPast⟩ := active_origin d coins T a ha
      have hTerm := (terminal_iff d T a haT).mpr hPast
      have hMin := finalStart_le_of_success d coins T a haT hTerm hStart.2
      omega

theorem finalStart_boundary (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    finalStart d coins T=T ∨ Terminal d T (finalStart d coins T) := by
  have hle := finalStart_le_horizon d coins T
  by_cases h : finalStart d coins T=T
  · exact Or.inl h
  · exact Or.inr (finalStart_success d coins T (by omega)).1

theorem roundStart_origin (d : ℕ → ℝ) (coins : ℕ → Bool) (n a : ℕ)
    (hRound : roundStart (state d coins n) n (coins n)=some a) :
    a≤n ∧ Starts d coins a ∧
      (∀ u, a<u → u≤n → cumulative d u<cumulative d a) ∧
      (∀ u, a≤u → u≤n → roundStart (state d coins u) u (coins u)=some a) := by
  rcases (roundStart_eq_some_iff (state d coins n) n a (coins n)).mp hRound with hOld | ⟨hNone,hCoin,ha⟩
  · obtain ⟨ha,hStart,_,hPast⟩ := active_origin d coins n a hOld
    refine ⟨ha.le,hStart,hPast,?_⟩
    intro u hau hun
    by_cases hEq : u=a
    · subst u
      exact (roundStart_eq_some_iff (state d coins a) a a (coins a)).mpr (Or.inr ⟨hStart.1,hStart.2,rfl⟩)
    · have hTerm := (terminal_iff d n a ha).mpr hPast
      have hActive := terminal_probe_continues d coins n a ha hStart hTerm u (by omega) hun
      exact (roundStart_eq_some_iff (state d coins u) u a (coins u)).mpr (Or.inl hActive)
  · subst a
    refine ⟨le_rfl,⟨hNone,hCoin⟩,?_,?_⟩
    · intro u hnu hun
      omega
    · intro u hnu hun
      have hEq : u=n := by omega
      simpa only [hEq] using hRound

end
end Tournament.Upper.GeometricProbing
