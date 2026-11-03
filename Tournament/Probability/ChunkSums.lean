module

public import Tournament.Probability.ChunkPartitions
public import Tournament.Probability.StoppedChunkCoupling

@[expose] public section

namespace Tournament.Restarts

open scoped Classical

noncomputable section

def chunkSum (q : ℕ → ℕ → ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | offset, n::ns => q offset n + chunkSum q (offset+(n+1)) ns

theorem plan_head_length (n : ℕ) (coins : Coins n) : (plan n coins).1=length n coins := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases coins with ⟨stop,rest⟩
    cases stop <;> simp [plan,length,ih rest]

theorem chunkSum_parts_step (q : ℕ → ℕ → ℝ) (offset n : ℕ) (stop : Bool) (rest : Coins n) :
    chunkSum q offset (parts (n+1) (stop,rest)) =
      if stop then q offset 0+chunkSum q (offset+1) (parts n rest)
      else q offset (length n rest+1)+chunkSum q (offset+1) (parts n rest)-q (offset+1) (length n rest) := by
  cases stop with
  | true => rfl
  | false =>
    change q offset ((plan n rest).1+1)+chunkSum q (offset+((plan n rest).1+1+1)) (plan n rest).2 =
      q offset (length n rest+1)+
        (q (offset+1) (plan n rest).1+chunkSum q ((offset+1)+((plan n rest).1+1)) (plan n rest).2)-
          q (offset+1) (length n rest)
    rw [plan_head_length]
    have hstart : offset+(length n rest+1+1)=(offset+1)+(length n rest+1) := by omega
    rw [hstart]
    ring

def firstChunkMean (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : ℕ → ℕ → ℝ) (n offset : ℕ) : ℝ :=
  (law τ hτ hτ1 n).mean (fun coins ↦ q offset (length n coins))

def chunkSumMean (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : ℕ → ℕ → ℝ) (n offset : ℕ) : ℝ :=
  (law τ hτ hτ1 n).mean (fun coins ↦ chunkSum q offset (parts n coins))

theorem firstChunkMean_step {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : ℕ → ℕ → ℝ) (n offset : ℕ) :
    firstChunkMean τ hτ hτ1 q (n+1) offset = τ*q offset 0 +
      (1-τ)*(law τ hτ hτ1 n).mean (fun coins ↦ q offset (length n coins+1)) := by
  unfold firstChunkMean
  change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
    (fun pair : Bool × Coins n ↦ q offset (length (n+1) pair)) = _
  rw [ProbabilityVector.joint_mean,coin_mean]
  change τ*(law τ hτ hτ1 n).mean (fun _ ↦ q offset 0)+
    (1-τ)*(law τ hτ hτ1 n).mean (fun coins ↦ q offset (length n coins+1)) = _
  rw [ProbabilityVector.mean_const]

theorem chunkSumMean_step {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : ℕ → ℕ → ℝ) (n offset : ℕ) :
    chunkSumMean τ hτ hτ1 q (n+1) offset = firstChunkMean τ hτ hτ1 q (n+1) offset +
      chunkSumMean τ hτ hτ1 q n (offset+1) - (1-τ)*firstChunkMean τ hτ hτ1 q n (offset+1) := by
  rw [chunkSumMean]
  change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
    (fun pair : Bool × Coins n ↦ chunkSum q offset (parts (n+1) pair)) = _
  rw [ProbabilityVector.joint_mean,coin_mean]
  have htrue : (fun rest : Coins n ↦ chunkSum q offset (parts (n+1) (true,rest))) =
      (fun rest ↦ q offset 0+chunkSum q (offset+1) (parts n rest)) := by
    funext rest
    exact chunkSum_parts_step q offset n true rest
  have hfalse : (fun rest : Coins n ↦ chunkSum q offset (parts (n+1) (false,rest))) =
      (fun rest ↦ q offset (length n rest+1)+chunkSum q (offset+1) (parts n rest)-q (offset+1) (length n rest)) := by
    funext rest
    exact chunkSum_parts_step q offset n false rest
  rw [htrue,hfalse,firstChunkMean_step]
  simp only [ProbabilityVector.mean_add,ProbabilityVector.mean_sub,ProbabilityVector.mean_const]
  unfold chunkSumMean firstChunkMean
  ring

theorem chunkSumMean_grouped_by_start {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (q : ℕ → ℕ → ℝ) (n offset : ℕ) :
    chunkSumMean τ hτ hτ1 q n offset = firstChunkMean τ hτ hτ1 q n offset +
      τ*(∑ t ∈ Finset.range n, firstChunkMean τ hτ hτ1 q (n-t-1) (offset+t+1)) := by
  induction n generalizing offset with
  | zero => simp [chunkSumMean,firstChunkMean,parts,plan,chunkSum,length]
  | succ n ih =>
    rw [chunkSumMean_step,ih (offset+1)]
    have hsum : (∑ t ∈ Finset.range (n+1), firstChunkMean τ hτ hτ1 q (n+1-t-1) (offset+t+1)) =
        firstChunkMean τ hτ hτ1 q n (offset+1)+
          ∑ t ∈ Finset.range n, firstChunkMean τ hτ hτ1 q (n-t-1) ((offset+1)+t+1) := by
      rw [Finset.sum_range_succ']
      have htail : (∑ t ∈ Finset.range n, firstChunkMean τ hτ hτ1 q (n+1-(t+1)-1) (offset+(t+1)+1)) =
          ∑ t ∈ Finset.range n, firstChunkMean τ hτ hτ1 q (n-t-1) ((offset+1)+t+1) := by
        apply Finset.sum_congr rfl
        intro t _
        have hleft : n+1-(t+1)-1=n-t-1 := by omega
        have hright : offset+(t+1)+1=(offset+1)+t+1 := by omega
        rw [hleft,hright]
      rw [htail]
      simp only [Nat.sub_zero,Nat.add_sub_cancel,Nat.add_zero]
      ring
    rw [hsum]
    ring

theorem chunkSumMean_le_of_fresh {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : ℕ → ℕ → ℝ)
    (hq : ∀ offset n, 0 ≤ q offset n) (δ : ℝ)
    (hfresh : ∀ offset n, firstChunkMean τ hτ hτ1 q n offset ≤ δ) (n offset : ℕ) :
    chunkSumMean τ hτ hτ1 q n offset ≤ ((n:ℝ)+1)*δ := by
  rw [chunkSumMean_grouped_by_start]
  have hδ : 0 ≤ δ := le_trans
    (ProbabilityVector.mean_nonneg (law τ hτ hτ1 0) (fun coins ↦ hq offset (length 0 coins))) (hfresh offset 0)
  have hfirst := hfresh offset n
  have hsum : (∑ t ∈ Finset.range n, firstChunkMean τ hτ hτ1 q (n-t-1) (offset+t+1)) ≤ (n:ℝ)*δ := by
    calc
      _ ≤ ∑ _t ∈ Finset.range n, δ := Finset.sum_le_sum (fun t _ ↦ hfresh (offset+t+1) (n-t-1))
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_left hsum hτ
  have hrate := mul_nonneg (sub_nonneg.mpr hτ1) (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ)
  nlinarith

theorem chunkSum_mono (q r : ℕ → ℕ → ℝ) (hqr : ∀ offset n, q offset n ≤ r offset n)
    (ns : List ℕ) (offset : ℕ) : chunkSum q offset ns ≤ chunkSum r offset ns := by
  induction ns generalizing offset with
  | nil => exact le_rfl
  | cons n ns ih => exact add_le_add (hqr offset n) (ih (offset+(n+1)))

theorem chunkSum_weighted_le (q : ℕ → ℕ → ℝ) (hq : ∀ offset n, 0 ≤ q offset n) (h : ℕ) :
    ∀ ns, totalRounds ns ≤ h → ∀ offset,
    chunkSum (fun offset n ↦ ((n:ℝ)+1)^2*q offset n) offset ns ≤
      (h:ℝ)^2*chunkSum q offset ns := by
  intro ns
  induction ns with
  | nil => intro _ offset; simp [chunkSum]
  | cons n ns ih =>
    intro hns offset
    have hhead : (n:ℝ)+1 ≤ h := by exact_mod_cast Nat.le_trans (head_rounds_le n ns) hns
    have hsquare : ((n:ℝ)+1)^2 ≤ (h:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hmul := mul_le_mul_of_nonneg_right hsquare (hq offset n)
    have htail := ih (Nat.le_trans (tail_rounds_le n ns) hns) (offset+(n+1))
    change ((n:ℝ)+1)^2*q offset n + chunkSum (fun offset n ↦ ((n:ℝ)+1)^2*q offset n) (offset+(n+1)) ns ≤
      (h:ℝ)^2*(q offset n+chunkSum q (offset+(n+1)) ns)
    rw [mul_add]
    exact add_le_add hmul htail

end
end Tournament.Restarts
