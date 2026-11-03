module

public import Tournament.Model.Concatenation

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*}

def prefixHorizon (length : ℕ → ℕ) (B : ℕ) : ℕ := ∑ b ∈ Finset.range B, length b

def scheduledBlockLoss (length : ℕ → ℕ) (loss : ℕ → ι → ℝ) (b : ℕ) (i : ι) : ℝ :=
  ∑ t ∈ Finset.range (length b), loss (prefixHorizon length b+t) i

def scheduledBlockCost [DecidableEq ι] (length : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (X : ℕ → ι) (b : ℕ) : ℝ :=
  accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t)) (fun t ↦ X (prefixHorizon length b+t))+
    (switchCount (length b) (fun t ↦ X (prefixHorizon length b+t)):ℝ)+1

theorem prefixHorizon_succ (length : ℕ → ℕ) (B : ℕ) :
    prefixHorizon length (B+1)=prefixHorizon length B+length B := Finset.sum_range_succ _ _

theorem appendActions_shift (h : ℕ) (X : ℕ → ι) : appendActions h X (fun t ↦ X (h+t))=X := by
  funext t
  unfold appendActions
  split
  · rfl
  · have heq : h+(t-h)=t := by omega
    exact congrArg X heq

theorem switchCount_append_le [DecidableEq ι] (h k : ℕ) (X Y : ℕ → ι) :
    switchCount (h+k) (appendActions h X Y)≤switchCount h X+switchCount k Y+1 := by
  cases h with
  | zero => simp [appendActions,switchCount]
  | succ n =>
    cases k with
    | zero => rw [Nat.add_zero,switchCount_append_prefix]; simp [switchCount]
    | succ m =>
      rw [switchCount_append]
      split <;> omega

theorem switchCount_split_le [DecidableEq ι] (h k : ℕ) (X : ℕ → ι) :
    switchCount (h+k) X≤switchCount h X+switchCount k (fun t ↦ X (h+t))+1 := by
  simpa only [appendActions_shift] using switchCount_append_le h k X (fun t ↦ X (h+t))

theorem scheduledBlockLoss_sum (length : ℕ → ℕ) (loss : ℕ → ι → ℝ) (B : ℕ) (i : ι) :
    (∑ b ∈ Finset.range B, scheduledBlockLoss length loss b i)=fixedLoss (prefixHorizon length B) loss i := by
  induction B with
  | zero => simp [prefixHorizon,fixedLoss]
  | succ B ih =>
    rw [Finset.sum_range_succ,ih,prefixHorizon_succ]
    unfold fixedLoss scheduledBlockLoss
    rw [Finset.sum_range_add]

theorem scheduledLoss_sum (length : ℕ → ℕ) (loss : ℕ → ι → ℝ) (B : ℕ) (X : ℕ → ι) :
    (∑ b ∈ Finset.range B, accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
      (fun t ↦ X (prefixHorizon length b+t)))=accumulatedLoss (prefixHorizon length B) loss X := by
  induction B with
  | zero => simp [prefixHorizon,accumulatedLoss]
  | succ B ih =>
    rw [Finset.sum_range_succ,ih,prefixHorizon_succ]
    unfold accumulatedLoss
    rw [Finset.sum_range_add]

theorem scheduledSwitches_cover [DecidableEq ι] (length : ℕ → ℕ) (B : ℕ) (X : ℕ → ι) :
    switchCount (prefixHorizon length B) X≤∑ b ∈ Finset.range B,
      (switchCount (length b) (fun t ↦ X (prefixHorizon length b+t))+1) := by
  induction B with
  | zero => simp [prefixHorizon,switchCount]
  | succ B ih =>
    rw [prefixHorizon_succ,Finset.sum_range_succ]
    have hs := switchCount_split_le (prefixHorizon length B) (length B) X
    omega

theorem scheduledCost_covers [DecidableEq ι] (length : ℕ → ℕ) (loss : ℕ → ι → ℝ) (B : ℕ) (X : ℕ → ι) :
    accumulatedLoss (prefixHorizon length B) loss X+(switchCount (prefixHorizon length B) X:ℝ)≤
      ∑ b ∈ Finset.range B, scheduledBlockCost length loss X b := by
  have hs : (switchCount (prefixHorizon length B) X:ℝ)≤∑ b ∈ Finset.range B,
      ((switchCount (length b) (fun t ↦ X (prefixHorizon length b+t)):ℝ)+1) := by
    exact_mod_cast scheduledSwitches_cover length B X
  unfold scheduledBlockCost
  have heq : (∑ b ∈ Finset.range B,
      (accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t)) (fun t ↦ X (prefixHorizon length b+t))+
        (switchCount (length b) (fun t ↦ X (prefixHorizon length b+t)):ℝ)+1))=
        accumulatedLoss (prefixHorizon length B) loss X+∑ b ∈ Finset.range B,
          ((switchCount (length b) (fun t ↦ X (prefixHorizon length b+t)):ℝ)+1) := by
    simp only [Finset.sum_add_distrib,scheduledLoss_sum]
    ring
  rw [heq]
  linarith

theorem scheduledBlockLoss_bounds (length : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t i, 0≤loss t i ∧ loss t i≤1) (b : ℕ) (i : ι) :
    0≤scheduledBlockLoss length loss b i ∧ scheduledBlockLoss length loss b i≤(length b:ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun t _ ↦ (hloss _ _).1)
  · calc
      _ ≤ ∑ _t ∈ Finset.range (length b), (1:ℝ) := Finset.sum_le_sum (fun t _ ↦ (hloss _ _).2)
      _ = _ := by simp

theorem scheduledBlockCost_bounds [DecidableEq ι] (length : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t i, 0≤loss t i ∧ loss t i≤1) (X : ℕ → ι) (b : ℕ) (hb : 0<length b) :
    0≤scheduledBlockCost length loss X b ∧ scheduledBlockCost length loss X b≤2*(length b:ℝ) := by
  have hL0 : 0≤accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
      (fun t ↦ X (prefixHorizon length b+t)) := Finset.sum_nonneg (fun t _ ↦ (hloss _ _).1)
  have hL1 : accumulatedLoss (length b) (fun t ↦ loss (prefixHorizon length b+t))
      (fun t ↦ X (prefixHorizon length b+t))≤(length b:ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range (length b), (1:ℝ) := Finset.sum_le_sum (fun t _ ↦ (hloss _ _).2)
      _ = _ := by simp
  have hs := switchCount_le (length b) (fun t ↦ X (prefixHorizon length b+t))
  have hsn : switchCount (length b) (fun t ↦ X (prefixHorizon length b+t))+1≤length b := by omega
  have hsr : (switchCount (length b) (fun t ↦ X (prefixHorizon length b+t)):ℝ)+1≤(length b:ℝ) := by exact_mod_cast hsn
  unfold scheduledBlockCost
  constructor
  · positivity
  · linarith

theorem pathRegret_norm_le [DecidableEq ι] [Fintype ι] [Nonempty ι] (T : ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t i, 0≤loss t i ∧ loss t i≤1) (X : ℕ → ι) : |pathRegret T loss X|≤2*(T:ℝ) := by
  have hL0 : 0≤accumulatedLoss T loss X := Finset.sum_nonneg (fun t _ ↦ (hloss t (X t)).1)
  have hL1 : accumulatedLoss T loss X≤(T:ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range T, (1:ℝ) := Finset.sum_le_sum (fun t _ ↦ (hloss t (X t)).2)
      _ = _ := by simp
  have hs : (switchCount T X:ℝ)≤(T:ℝ) := by exact_mod_cast le_trans (switchCount_le T X) (Nat.sub_le T 1)
  have hb0 := bestFixedLoss_nonneg T loss (fun t _ i ↦ (hloss t i).1)
  obtain ⟨i,hi⟩ := exists_bestFixedLoss T loss
  have hb1 : bestFixedLoss T loss≤(T:ℝ) := by rw [hi]; exact fixedLoss_le_horizon T loss i (fun t _ j ↦ (hloss t j).2)
  unfold pathRegret
  apply abs_le.mpr
  constructor <;> nlinarith [show (0:ℝ)≤(switchCount T X:ℝ) by positivity]

end
end Tournament.Model
