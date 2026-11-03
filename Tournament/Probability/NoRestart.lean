module

public import Tournament.Probability.StoppedChunkCoupling
public import Tournament.Probability.ExponentialTail

@[expose] public section

namespace Tournament.Restarts

open scoped Classical

noncomputable section

def coinAt : (n : ℕ) → Coins n → ℕ → Bool
  | 0, _, _ => false
  | _n+1, (stop,_), 0 => stop
  | n+1, (_,rest), t+1 => coinAt n rest t

def noRestart (n : ℕ) (coins : Coins n) (i j : ℕ) : Prop :=
  ∀ t, i ≤ t → t<j → coinAt n coins t=false

theorem noRestart_self (n : ℕ) (coins : Coins n) (i : ℕ) : noRestart n coins i i := by
  intro t ht ht'
  omega

theorem noRestart_zero_succ (stop : Bool) (n : ℕ) (rest : Coins n) (j : ℕ) :
    noRestart (n+1) (stop,rest) 0 (j+1) ↔ stop=false ∧ noRestart n rest 0 j := by
  constructor
  · intro h
    refine ⟨h 0 le_rfl (by omega), ?_⟩
    intro t ht ht'
    exact h (t+1) (by omega) (by omega)
  · rintro ⟨hstop,hrest⟩ t ht ht'
    cases t with
    | zero => exact hstop
    | succ t => exact hrest t (by omega) (by omega)

theorem noRestart_succ_succ (stop : Bool) (n : ℕ) (rest : Coins n) (i j : ℕ) :
    noRestart (n+1) (stop,rest) (i+1) (j+1) ↔ noRestart n rest i j := by
  constructor
  · intro h t ht ht'
    exact h (t+1) (by omega) (by omega)
  · intro h t ht ht'
    cases t with
    | zero => omega
    | succ t => exact h t (by omega) (by omega)

theorem noRestart_probability_self {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n i : ℕ) :
    (law τ hτ hτ1 n).probability (fun coins ↦ noRestart n coins i i) = 1 := by
  unfold ProbabilityVector.probability
  have heq : (fun coins : Coins n ↦ if noRestart n coins i i then (1:ℝ) else 0) = (fun _ ↦ 1) := by
    funext coins
    rw [ite_eq_left (noRestart_self n coins i)]
  rw [heq, ProbabilityVector.mean_const]

theorem noRestart_probability {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (law τ hτ hτ1 n).probability (fun coins ↦ noRestart n coins i j) = (1-τ)^(j-i) := by
  induction n generalizing i j with
  | zero =>
    have hj : j=0 := Nat.eq_zero_of_le_zero hjn
    have hi : i=0 := by omega
    subst j
    subst i
    simpa only [Nat.sub_self, pow_zero] using noRestart_probability_self hτ hτ1 0 0
  | succ n ih =>
    cases j with
    | zero =>
      have hi : i=0 := Nat.eq_zero_of_le_zero hij
      subst i
      simpa only [Nat.sub_self, pow_zero] using noRestart_probability_self hτ hτ1 (n+1) 0
    | succ j =>
      cases i with
      | zero =>
        unfold ProbabilityVector.probability
        change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
          (fun pair : Bool × Coins n ↦ if noRestart (n+1) pair 0 (j+1) then 1 else 0) = _
        rw [ProbabilityVector.joint_mean, coin_mean]
        have htrue : (fun rest : Coins n ↦ if noRestart (n+1) (true,rest) 0 (j+1) then (1:ℝ) else 0) =
            (fun _ ↦ 0) := by
          funext rest
          simp [noRestart_zero_succ]
        have hfalse : (fun rest : Coins n ↦ if noRestart (n+1) (false,rest) 0 (j+1) then (1:ℝ) else 0) =
            (fun rest ↦ if noRestart n rest 0 j then 1 else 0) := by
          funext rest
          simp [noRestart_zero_succ]
        rw [htrue,hfalse,ProbabilityVector.mean_const,mul_zero,zero_add]
        change (1-τ)*(law τ hτ hτ1 n).probability (fun coins ↦ noRestart n coins 0 j) = _
        rw [ih 0 j (Nat.zero_le j) (by omega)]
        simp only [Nat.sub_zero,pow_succ]
        ring
      | succ i =>
        unfold ProbabilityVector.probability
        change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
          (fun pair : Bool × Coins n ↦ if noRestart (n+1) pair (i+1) (j+1) then 1 else 0) = _
        have heq : (fun pair : Bool × Coins n ↦ if noRestart (n+1) pair (i+1) (j+1) then (1:ℝ) else 0) =
            (fun pair ↦ if noRestart n pair.2 i j then 1 else 0) := by
          funext pair
          rw [noRestart_succ_succ]
        rw [heq,ProbabilityVector.joint_mean]
        change (coin τ hτ hτ1).mean (fun _ ↦ (law τ hτ hτ1 n).probability (fun coins ↦ noRestart n coins i j)) = _
        rw [ProbabilityVector.mean_const]
        have h := ih i j (by omega) (by omega)
        simpa only [Nat.add_sub_add_right] using h

end
end Tournament.Restarts
