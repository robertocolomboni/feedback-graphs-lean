module

public import Tournament.Probability.Restarts

@[expose] public section

namespace Tournament.Restarts

noncomputable section

def totalRounds : List ℕ → ℕ
  | [] => 0
  | n::ns => (n+1)+totalRounds ns

def plan : (n : ℕ) → Coins n → ℕ × List ℕ
  | 0, _ => (0,[])
  | n+1, (stop,rest) =>
      let p := plan n rest
      if stop then (0,p.1::p.2) else (p.1+1,p.2)

def parts (n : ℕ) (coins : Coins n) : List ℕ := (plan n coins).1 :: (plan n coins).2

theorem parts_nonempty (n : ℕ) (coins : Coins n) : parts n coins ≠ [] := List.cons_ne_nil _ _

theorem parts_totalRounds (n : ℕ) (coins : Coins n) : totalRounds (parts n coins) = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases coins with ⟨stop,rest⟩
    have h := ih rest
    cases stop <;> simp only [parts, plan, Bool.false_eq_true, ite_false, ite_true,
      totalRounds] at h ⊢ <;> omega

theorem head_rounds_le (n : ℕ) (ns : List ℕ) : n+1 ≤ totalRounds (n::ns) :=
  Nat.le_add_right _ _

theorem tail_rounds_le (n : ℕ) (ns : List ℕ) : totalRounds ns ≤ totalRounds (n::ns) :=
  Nat.le_add_left _ _

end
end Tournament.Restarts
