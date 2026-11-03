module

public import Tournament.Probability.ChunkPartitions
public import Tournament.Probability.NoRestart

@[expose] public section

namespace Tournament.Restarts

open scoped Classical

noncomputable section

def chunkIndex : List ℕ → ℕ → ℕ
  | [], _ => 0
  | n::ns, t => if t<n+1 then 0 else 1+chunkIndex ns (t-(n+1))

theorem chunkIndex_parts_zero (n : ℕ) (coins : Coins n) : chunkIndex (parts n coins) 0=0 := by
  change (if 0<(plan n coins).1+1 then 0 else 1+chunkIndex (plan n coins).2 (0-((plan n coins).1+1))) = 0
  rw [ite_eq_left (by omega)]

theorem chunkIndex_parts_succ (n : ℕ) (stop : Bool) (rest : Coins n) (t : ℕ) :
    chunkIndex (parts (n+1) (stop,rest)) (t+1) =
      if stop then 1+chunkIndex (parts n rest) t else chunkIndex (parts n rest) t := by
  cases stop with
  | true =>
    change (if t+1<1 then 0 else 1+chunkIndex (parts n rest) (t+1-1)) = 1+chunkIndex (parts n rest) t
    rw [ite_eq_right (by omega),Nat.add_sub_cancel]
  | false =>
    change (if t+1<(plan n rest).1+1+1 then 0 else
        1+chunkIndex (plan n rest).2 (t+1-((plan n rest).1+1+1))) =
      (if t<(plan n rest).1+1 then 0 else 1+chunkIndex (plan n rest).2 (t-((plan n rest).1+1)))
    by_cases h : t<(plan n rest).1+1
    · rw [ite_eq_left h,ite_eq_left (by omega)]
    · rw [ite_eq_right h,ite_eq_right (by omega)]
      have hdiff : t+1-((plan n rest).1+1+1)=t-((plan n rest).1+1) := by omega
      rw [hdiff]

theorem chunkIndex_eq_iff_noRestart (n : ℕ) (coins : Coins n) (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    chunkIndex (parts n coins) i=chunkIndex (parts n coins) j ↔ noRestart n coins i j := by
  induction n generalizing i j with
  | zero =>
    have hj0 : j=0 := Nat.eq_zero_of_le_zero hjn
    have hi0 : i=0 := by omega
    subst j
    subst i
    exact ⟨fun _ ↦ noRestart_self 0 coins 0,fun _ ↦ rfl⟩
  | succ n ih =>
    rcases coins with ⟨stop,rest⟩
    cases j with
    | zero =>
      have hi0 : i=0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact ⟨fun _ ↦ noRestart_self (n+1) (stop,rest) 0,fun _ ↦ rfl⟩
    | succ j =>
      cases i with
      | zero =>
        rw [chunkIndex_parts_zero,chunkIndex_parts_succ,noRestart_zero_succ]
        cases stop with
        | true => simp [Nat.one_add]
        | false =>
          simp only [Bool.false_eq_true,ite_false,true_and]
          have h := ih rest 0 j (Nat.zero_le j) (by omega)
          rw [chunkIndex_parts_zero] at h
          exact h
      | succ i =>
        rw [chunkIndex_parts_succ,chunkIndex_parts_succ,noRestart_succ_succ]
        cases stop with
        | true =>
          simp only [ite_true,Nat.add_left_cancel_iff]
          exact ih rest i j (by omega) (by omega)
        | false =>
          simp only [Bool.false_eq_true,ite_false]
          exact ih rest i j (by omega) (by omega)

theorem same_chunk_probability {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n i j : ℕ)
    (hij : i ≤ j) (hjn : j ≤ n) :
    (law τ hτ hτ1 n).probability (fun coins ↦ chunkIndex (parts n coins) i=chunkIndex (parts n coins) j) =
      (1-τ)^(j-i) := by
  have heq : (fun coins : Coins n ↦ chunkIndex (parts n coins) i=chunkIndex (parts n coins) j) =
      (fun coins ↦ noRestart n coins i j) := by
    funext coins
    exact propext (chunkIndex_eq_iff_noRestart n coins i j hij hjn)
  rw [heq,noRestart_probability hτ hτ1 n i j hij hjn]

end
end Tournament.Restarts
