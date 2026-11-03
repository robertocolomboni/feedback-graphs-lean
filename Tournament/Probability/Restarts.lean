module

public import Tournament.Probability.FinitePath
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω : Type*} [Fintype Ω] {β : Ω → Type*} [∀ x, Fintype (β x)]

def sigmaJoint (μ : ProbabilityVector Ω) (κ : (x : Ω) → ProbabilityVector (β x)) :
    ProbabilityVector (Sigma β) where
  weight x := μ x.1 * κ x.1 x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((κ x.1).nonneg x.2)
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    calc
      (∑ x, ∑ y, μ x * κ x y) = ∑ x, μ x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum, (κ x).sum_eq_one, mul_one]
      _ = 1 := μ.sum_eq_one

theorem sigmaJoint_mean (μ : ProbabilityVector Ω) (κ : (x : Ω) → ProbabilityVector (β x))
    (f : Sigma β → ℝ) :
    (μ.sigmaJoint κ).mean f = μ.mean (fun x ↦ (κ x).mean (fun y ↦ f ⟨x,y⟩)) := by
  unfold mean sigmaJoint
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end ProbabilityVector

namespace Restarts

def coin (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) : ProbabilityVector Bool where
  weight b := if b then τ else 1-τ
  nonneg b := by cases b <;> simp <;> linarith
  sum_eq_one := by simp

abbrev Coins : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Coins n

instance coinsFintype (n : ℕ) : Fintype (Coins n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Coins n) := ih
    exact inferInstanceAs (Fintype (Bool × Coins n))

def law (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) : (n : ℕ) → ProbabilityVector (Coins n)
  | 0 => ⟨fun _ ↦ 1, fun _ ↦ zero_le_one, by
      change (∑ _ : Unit, (1:ℝ)) = 1
      simp⟩
  | n+1 => (coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)

def length : (n : ℕ) → Coins n → ℕ
  | 0, _ => 0
  | n+1, (stop,rest) => if stop then 0 else length n rest+1

theorem length_le (n : ℕ) (coins : Coins n) : length n coins ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases coins with ⟨stop,rest⟩
    cases stop <;> simp only [length, Bool.false_eq_true, ite_false, ite_true]
    · have h := ih rest
      omega
    · omega

theorem expected_length_step {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (law τ hτ hτ1 (n+1)).mean (fun coins ↦ (length (n+1) coins : ℝ)) =
      (1-τ) * (1+(law τ hτ hτ1 n).mean (fun coins ↦ (length n coins : ℝ))) := by
  change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
    (fun coins : Bool × Coins n ↦ (length (n+1) coins : ℝ)) = _
  rw [ProbabilityVector.joint_mean]
  have hf : (fun stop ↦ (law τ hτ hτ1 n).mean
      (fun rest ↦ (length (n+1) (stop,rest) : ℝ))) =
      (fun stop ↦ if stop then 0 else 1+(law τ hτ hτ1 n).mean (fun rest ↦ (length n rest : ℝ))) := by
    funext stop
    cases stop <;> simp [length, Nat.cast_add, ProbabilityVector.mean_add, add_comm]
  rw [hf]
  simp [ProbabilityVector.mean, coin]

theorem expected_length_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦ (length n coins : ℝ)) ≤ 1/τ := by
  induction n with
  | zero =>
    have hzero : (fun coins : Coins 0 ↦ (length 0 coins : ℝ)) = (fun _ ↦ 0) := by
      funext coins
      simp [length]
    rw [hzero, ProbabilityVector.mean_const]
    positivity
  | succ n ih =>
    rw [expected_length_step]
    have hmul := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hτ1)
    have hid : (1-τ)*(1+1/τ) = 1/τ-τ := by
      field_simp
      ring
    calc
      (1-τ)*(1+(law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦ (length n coins : ℝ))) ≤
          (1-τ)*(1+1/τ) := by linarith
      _ = 1/τ-τ := hid
      _ ≤ 1/τ := by linarith

variable {ι : Type*} [Fintype ι]

abbrev ChunkOutcome (ι : Type*) (n : ℕ) := (coins : Coins n) × FinitePath.History ι (length n coins)

instance chunkOutcomeFintype (n : ℕ) : Fintype (ChunkOutcome ι n) :=
  inferInstanceAs (Fintype ((coins : Coins n) × FinitePath.History ι (length n coins)))

def referenceChunkLaw (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) : ProbabilityVector (ChunkOutcome ι n) :=
  (law τ hτ hτ1 n).sigmaJoint (fun coins ↦ FinitePath.law P μ (length n coins))

theorem referenceChunk_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) (f : ChunkOutcome ι n → ℝ) :
    (referenceChunkLaw P μ τ hτ hτ1 n).mean f =
      (law τ hτ hτ1 n).mean (fun coins ↦
        (FinitePath.law P μ (length n coins)).mean (fun hist ↦ f ⟨coins,hist⟩)) :=
  ProbabilityVector.sigmaJoint_mean _ _ _

end Restarts
end
end Tournament
