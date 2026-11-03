module

public import Tournament.Upper.GeometricTerminal

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open scoped Classical
noncomputable section

structure ProbeState where
  start : Option ℕ
  balance : ℝ

def resting : ProbeState := ⟨none,0⟩

def roundStart (s : ProbeState) (t : ℕ) (coin : Bool) : Option ℕ :=
  match s.start with
  | some a => some a
  | none => if coin then some t else none

def advance (s : ProbeState) (t : ℕ) (coin : Bool) (z : ℝ) : ProbeState :=
  match roundStart s t coin with
  | none => resting
  | some a => if s.balance+z<0 then ⟨some a,s.balance+z⟩ else resting

def state (d : ℕ → ℝ) (coins : ℕ → Bool) : ℕ → ProbeState
  | 0 => resting
  | n+1 => advance (state d coins n) n (coins n) (d n)

def Playing (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) : Prop :=
  (roundStart (state d coins t) t (coins t)).isSome=true

def Starts (d : ℕ → ℝ) (coins : ℕ → Bool) (t : ℕ) : Prop :=
  (state d coins t).start=none ∧ coins t=true

theorem roundStart_eq_some_iff (q : ProbeState) (t a : ℕ) (coin : Bool) :
    roundStart q t coin=some a ↔ q.start=some a ∨ (q.start=none ∧ coin=true ∧ a=t) := by
  cases h : q.start <;> cases coin <;> simp [roundStart,h,eq_comm]

theorem roundStart_none_iff (q : ProbeState) (t : ℕ) (coin : Bool) :
    roundStart q t coin=none ↔ q.start=none ∧ coin=false := by
  cases h : q.start <;> cases coin <;> simp [roundStart,h]

theorem state_succ_active_iff (d : ℕ → ℝ) (coins : ℕ → Bool) (n a : ℕ) :
    (state d coins (n+1)).start=some a ↔
      roundStart (state d coins n) n (coins n)=some a ∧ (state d coins n).balance+d n<0 := by
  cases hr : roundStart (state d coins n) n (coins n) with
  | none => simp [state,advance,hr,resting]
  | some b =>
    by_cases h : (state d coins n).balance+d n<0
    · simp [state,advance,hr,h]
    · simp [state,advance,hr,h,resting]

theorem state_succ_balance (d : ℕ → ℝ) (coins : ℕ → Bool) (n a : ℕ)
    (h : (state d coins (n+1)).start=some a) :
    (state d coins (n+1)).balance=(state d coins n).balance+d n := by
  obtain ⟨hr,hb⟩ := (state_succ_active_iff d coins n a).mp h
  simp only [state,advance,hr,ite_eq_left hb]

theorem state_normal (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    ((state d coins n).start=none ∧ (state d coins n).balance=0) ∨
      ∃ a, (state d coins n).start=some a ∧ (state d coins n).balance<0 := by
  cases n with
  | zero => exact Or.inl ⟨rfl,rfl⟩
  | succ n =>
    cases hr : roundStart (state d coins n) n (coins n) with
    | none => left; simp [state,advance,hr,resting]
    | some a =>
      by_cases hb : (state d coins n).balance+d n<0
      · right
        exact ⟨a,by simp [state,advance,hr,hb],by simpa only [state,advance,hr,ite_eq_left hb] using hb⟩
      · left
        simp [state,advance,hr,hb,resting]

theorem state_none_balance (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ)
    (h : (state d coins n).start=none) : (state d coins n).balance=0 := by
  rcases state_normal d coins n with h0 | ⟨a,ha,_⟩
  · exact h0.2
  · rw [h] at ha
    cases ha

theorem state_some_negative (d : ℕ → ℝ) (coins : ℕ → Bool) (n a : ℕ)
    (h : (state d coins n).start=some a) : (state d coins n).balance<0 := by
  rcases state_normal d coins n with h0 | ⟨b,_,hb⟩
  · rw [h0.1] at h
    cases h
  · exact hb

theorem state_balance_nonpos (d : ℕ → ℝ) (coins : ℕ → Bool) (n : ℕ) :
    (state d coins n).balance≤0 := by
  rcases state_normal d coins n with h0 | ⟨_,_,hb⟩
  · exact le_of_eq h0.2
  · exact hb.le

theorem active_origin (d : ℕ → ℝ) (coins : ℕ → Bool) (n a : ℕ)
    (h : (state d coins n).start=some a) :
    a<n ∧ Starts d coins a ∧
      (state d coins n).balance=cumulative d n-cumulative d a ∧
      (∀ u, a<u → u≤n → cumulative d u<cumulative d a) := by
  induction n generalizing a with
  | zero => simp [state,resting] at h
  | succ n ih =>
    obtain ⟨hr,_⟩ := (state_succ_active_iff d coins n a).mp h
    rcases (roundStart_eq_some_iff (state d coins n) n a (coins n)).mp hr with hOld | ⟨hNone,hCoin,ha⟩
    · obtain ⟨ha,hStart,hBalance,hBefore⟩ := ih a hOld
      have hDiff : (state d coins (n+1)).balance=cumulative d (n+1)-cumulative d a := by
        rw [state_succ_balance d coins n a h,hBalance,prefix_succ]
        ring
      have hNext : cumulative d (n+1)<cumulative d a := by
        have hNeg := state_some_negative d coins (n+1) a h
        rw [hDiff] at hNeg
        linarith
      refine ⟨by omega,hStart,hDiff,?_⟩
      intro u hau hun
      by_cases hu : u≤n
      · exact hBefore u hau hu
      · have huEq : u=n+1 := by omega
        simpa only [huEq] using hNext
    · subst a
      have hDiff : (state d coins (n+1)).balance=cumulative d (n+1)-cumulative d n := by
        rw [state_succ_balance d coins n n h,state_none_balance d coins n hNone,prefix_succ]
        ring
      have hNext : cumulative d (n+1)<cumulative d n := by
        have hNeg := state_some_negative d coins (n+1) n h
        rw [hDiff] at hNeg
        linarith
      refine ⟨by omega,⟨hNone,hCoin⟩,hDiff,?_⟩
      intro u hnu hun
      have huEq : u=n+1 := by omega
      simpa only [huEq] using hNext

theorem state_eq_of_past_coins (d : ℕ → ℝ) (coins other : ℕ → Bool) (n : ℕ)
    (hPast : ∀ t<n, coins t=other t) : state d coins n=state d other n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [state,state,ih (fun t ht ↦ hPast t (by omega)),hPast n (by omega)]

theorem advance_eq_of_not_playing (q : ProbeState) (t : ℕ) (coin : Bool) (z z' : ℝ)
    (h : roundStart q t coin=none) : advance q t coin z=advance q t coin z' := by
  simp only [advance,h]

end
end Tournament.Upper.GeometricProbing
