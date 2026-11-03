module

public import Tournament.Upper.DyadicPrefixLocality
public import Tournament.Upper.FeedbackLocality
public import Tournament.Probability.ExecutionEncoding

@[expose] public section

namespace Tournament.Model.FeedbackEW

open scoped BigOperators Classical
open Upper Upper.ExponentialWeights

noncomputable section

variable {ι : Type*} {m : ℕ}

abbrev ExecutionHistory (ι : Type*) (m : ℕ) (n : ℕ → ℕ) (B : ℕ) :=
  FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B

def executionPath (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n B) : ℕ → ι :=
  ScheduledExecution.trajectory default (fun b ↦ n b+1)
    (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B x

def executionMetadata (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n B) : metadataHistory m n B :=
  (executionTraceEquiv (ι := ι) m n B x).1

theorem executionPath_succ_prefix (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n (B+1)) (s : ℕ)
    (hs : s < prefixHorizon (fun b ↦ n b+1) B) :
    executionPath default n (B+1) x s = executionPath default n B x.1 s := by
  simp only [executionPath, ScheduledExecution.trajectory, appendActions, ite_eq_left hs]

theorem executionPath_succ_tail (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : ExecutionHistory ι m n (B+1)) (s : ℕ) :
    executionPath default n (B+1) x (prefixHorizon (fun b ↦ n b+1) B+s) =
      blockActions default (Restarts.parts (n B) x.2.2.1) x.2.2.2 s := by
  simp only [executionPath, ScheduledExecution.trajectory, appendActions,
    ite_eq_right (by omega : ¬prefixHorizon (fun b ↦ n b+1) B+s <
      prefixHorizon (fun b ↦ n b+1) B), Nat.add_sub_cancel_left]

def metadataPrefixEvent (default : ι) (n : ℕ → ℕ) (B t : ℕ)
    (a x : ExecutionHistory ι m n B) : Prop :=
  executionMetadata n B x = executionMetadata n B a ∧
    SameActionPrefix t (executionPath default n B x) (executionPath default n B a)

theorem metadataPrefixEvent_full (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (a x : ExecutionHistory ι m n B) :
    metadataPrefixEvent default n B (prefixHorizon (fun b ↦ n b+1) B) a x ↔ x = a := by
  constructor
  · rintro ⟨hmeta,hpath⟩
    apply (executionTraceEquiv (ι := ι) m n B).injective
    apply Prod.ext hmeta
    funext i
    rw [executionTrace_eq_actions default, executionTrace_eq_actions default]
    exact hpath i.val i.isLt
  · rintro rfl
    exact ⟨rfl,fun _ _ ↦ rfl⟩

theorem metadataPrefixEvent_succ_le (default : ι) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B)
    (a x : ExecutionHistory ι m n (B+1)) :
    metadataPrefixEvent default n (B+1) t a x ↔
      metadataPrefixEvent default n B t a.1 x.1 ∧ (x.2.1,x.2.2.1) = (a.2.1,a.2.2.1) := by
  change ((executionMetadata n B x.1,(x.2.1,x.2.2.1)) =
      (executionMetadata n B a.1,(a.2.1,a.2.2.1)) ∧
    SameActionPrefix t
      (appendActions (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x.1)
        (blockActions default (Restarts.parts (n B) x.2.2.1) x.2.2.2))
      (appendActions (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B a.1)
        (blockActions default (Restarts.parts (n B) a.2.2.1) a.2.2.2))) ↔ _
  rw [sameActionPrefix_append_le _ _ ht]
  simp only [Prod.mk.injEq, metadataPrefixEvent]
  tauto

theorem metadataPrefixEvent_succ_ge (default : ι) (n : ℕ → ℕ) (B t : ℕ)
    (ht : prefixHorizon (fun b ↦ n b+1) B ≤ t)
    (a x : ExecutionHistory ι m n (B+1)) :
    metadataPrefixEvent default n (B+1) t a x ↔
      x.1 = a.1 ∧ ((x.2.1,x.2.2.1) = (a.2.1,a.2.2.1) ∧
        SameActionPrefix (t-prefixHorizon (fun b ↦ n b+1) B)
          (blockActions default (Restarts.parts (n B) x.2.2.1) x.2.2.2)
          (blockActions default (Restarts.parts (n B) a.2.2.1) a.2.2.2)) := by
  change ((executionMetadata n B x.1,(x.2.1,x.2.2.1)) =
      (executionMetadata n B a.1,(a.2.1,a.2.2.1)) ∧
    SameActionPrefix t
      (appendActions (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B x.1)
        (blockActions default (Restarts.parts (n B) x.2.2.1) x.2.2.2))
      (appendActions (prefixHorizon (fun b ↦ n b+1) B) (executionPath default n B a.1)
        (blockActions default (Restarts.parts (n B) a.2.2.1) a.2.2.2))) ↔ _
  rw [sameActionPrefix_append_ge _ _ ht]
  rw [← metadataPrefixEvent_full default n B a.1 x.1]
  simp only [Prod.mk.injEq, metadataPrefixEvent]
  tauto

variable [Fintype ι] [Nonempty ι]

def MetadataIndependent (P : FeedbackEW ι m) : Prop :=
  ∀ (p q : ProbabilityVector ι) n j coins,
    (P.policy p).metadataWeight n (j,coins) = (P.policy q).metadataWeight n (j,coins)

def executionPrefixMass (P : FeedbackEW ι m) (default : ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B t : ℕ)
    (a : ExecutionHistory ι m n B) : ℝ :=
  (P.algorithm F n loss).execution B |>.mean
    (fun x ↦ if metadataPrefixEvent default n B t a x then 1 else 0)

theorem executionPrefixMass_succ_le (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent)
    (default : ι) (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n : ℕ → ℕ)
    (B t : ℕ) (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B)
    (a : ExecutionHistory ι m n (B+1)) :
    P.executionPrefixMass default F loss n (B+1) t a =
      P.executionPrefixMass default F loss n B t a.1 *
        (P.policy uniform).metadataWeight (n B) (a.2.1,a.2.2.1) := by
  unfold executionPrefixMass
  change (((P.algorithm F n loss).execution B).joint
    ((P.algorithm F n loss).kernel B)).mean _ = _
  simp_rw [metadataPrefixEvent_succ_le default n B t ht]
  rw [ProbabilityVector.joint_mean]
  have hinner (x : ExecutionHistory ι m n B) :
      ((P.algorithm F n loss).kernel B x).mean (fun y ↦
        if metadataPrefixEvent default n B t a.1 x ∧ (y.1,y.2.1) = (a.2.1,a.2.2.1)
          then 1 else 0) =
      (if metadataPrefixEvent default n B t a.1 x then 1 else 0) *
        (P.policy uniform).metadataWeight (n B) (a.2.1,a.2.2.1) := by
    by_cases hx : metadataPrefixEvent default n B t a.1 x
    · simp only [hx, true_and, ite_true, one_mul]
      have hzero := (P.policy ((P.algorithm F n loss).distribution B x)).metadataPrefixMass_zero
        default F loss (prefixHorizon (fun b ↦ n b+1) B) (n B) a.2
      simp only [RestartComparisonPolicy.metadataPrefixMass, SameActionPrefix,
        Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true] at hzero
      exact hzero.trans (hMeta _ uniform (n B) a.2.1 a.2.2.1)
    · simp only [hx, false_and, ite_false, ProbabilityVector.mean_const, zero_mul]
  simp_rw [hinner]
  exact ProbabilityVector.mean_mul_const _ _ _

theorem executionPrefixMass_succ_ge (P : FeedbackEW ι m)
    (default : ι) (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n : ℕ → ℕ)
    (B t : ℕ) (ht : prefixHorizon (fun b ↦ n b+1) B ≤ t)
    (a : ExecutionHistory ι m n (B+1)) :
    P.executionPrefixMass default F loss n (B+1) t a =
      (P.algorithm F n loss).execution B a.1 *
        (P.policy ((P.algorithm F n loss).distribution B a.1)).metadataPrefixMass
          default F loss (prefixHorizon (fun b ↦ n b+1) B) (n B)
          (t-prefixHorizon (fun b ↦ n b+1) B) a.2 := by
  unfold executionPrefixMass
  change (((P.algorithm F n loss).execution B).joint
    ((P.algorithm F n loss).kernel B)).mean _ = _
  simp_rw [metadataPrefixEvent_succ_ge default n B t ht]
  rw [ProbabilityVector.joint_mean]
  simp [ProbabilityVector.mean, RestartComparisonPolicy.metadataPrefixMass,
    mul_ite, ite_and]
  exact Or.inl rfl

set_option maxHeartbeats 800000 in
theorem executionPrefixMass_eq_of_observations_succ (P : FeedbackEW ι m)
    (hMeta : P.MetadataIndependent) (default : ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ)
    (ih : ∀ t, t ≤ prefixHorizon (fun b ↦ n b+1) B →
      ∀ a : ExecutionHistory ι m n B,
      (∀ s, s+1 < t → comparisonObservation F (executionPath default n B a s) (loss s) =
        comparisonObservation F (executionPath default n B a s) (loss' s)) →
      P.executionPrefixMass default F loss n B t a =
        P.executionPrefixMass default F loss' n B t a)
    (t : ℕ) (ht : t ≤ prefixHorizon (fun b ↦ n b+1) (B+1))
    (a : ExecutionHistory ι m n (B+1))
    (hobs : ∀ s, s+1 < t → comparisonObservation F (executionPath default n (B+1) a s) (loss s) =
      comparisonObservation F (executionPath default n (B+1) a s) (loss' s)) :
    P.executionPrefixMass default F loss n (B+1) t a =
      P.executionPrefixMass default F loss' n (B+1) t a := by
    by_cases htB : t ≤ prefixHorizon (fun b ↦ n b+1) B
    · have hpre : P.executionPrefixMass default F loss n B t a.1 =
          P.executionPrefixMass default F loss' n B t a.1 := by
        apply ih t htB a.1
        intro s hs
        have hsB : s < prefixHorizon (fun b ↦ n b+1) B := by omega
        have ho := hobs s hs
        rw [executionPath_succ_prefix default n B a s hsB] at ho
        exact ho
      exact (executionPrefixMass_succ_le P hMeta default F loss n B t htB a).trans
        ((congrArg (fun z : ℝ ↦ z * (P.policy uniform).metadataWeight (n B) (a.2.1,a.2.2.1)) hpre).trans
          (executionPrefixMass_succ_le P hMeta default F loss' n B t htB a).symm)
    · have hBt : prefixHorizon (fun b ↦ n b+1) B ≤ t := by omega
      have hprev : ObservationsAgree F loss loss' default n B a.1 := by
        intro s hs
        have ho := hobs s (by omega)
        rw [executionPath_succ_prefix default n B a s hs] at ho
        exact ho
      have hdist := distribution_eq_of_observations P F loss loss' default n B a.1 hprev
      have hweight := execution_atom_eq_of_observations P F loss loss' default n B a.1 hprev
      have hrow :
          (P.policy ((P.algorithm F n loss').distribution B a.1)).metadataPrefixMass
            default F loss (prefixHorizon (fun b ↦ n b+1) B) (n B)
            (t-prefixHorizon (fun b ↦ n b+1) B) a.2 =
          (P.policy ((P.algorithm F n loss').distribution B a.1)).metadataPrefixMass
            default F loss' (prefixHorizon (fun b ↦ n b+1) B) (n B)
            (t-prefixHorizon (fun b ↦ n b+1) B) a.2 := by
        apply RestartComparisonPolicy.metadataPrefixMass_eq_of_observations
        · rw [prefixHorizon_succ] at ht
          omega
        · intro s hs
          have ho := hobs (prefixHorizon (fun b ↦ n b+1) B+s) (by omega)
          rw [executionPath_succ_tail default n B a s] at ho
          exact ho
      have hcurrent := (congrArg (fun p : ProbabilityVector ι ↦
        (P.policy p).metadataPrefixMass default F loss
          (prefixHorizon (fun b ↦ n b+1) B) (n B)
          (t-prefixHorizon (fun b ↦ n b+1) B) a.2) hdist).trans hrow
      exact (executionPrefixMass_succ_ge P default F loss n B t hBt a).trans
        ((congrArg₂ (fun x y : ℝ ↦ x*y) hweight hcurrent).trans
          (executionPrefixMass_succ_ge P default F loss' n B t hBt a).symm)

def PrefixLocalAt (P : FeedbackEW ι m) (default : ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ t, t ≤ prefixHorizon (fun b ↦ n b+1) B →
    ∀ a : ExecutionHistory ι m n B,
    (∀ s, s+1 < t → comparisonObservation F (executionPath default n B a s) (loss s) =
      comparisonObservation F (executionPath default n B a s) (loss' s)) →
    P.executionPrefixMass default F loss n B t a =
      P.executionPrefixMass default F loss' n B t a

theorem prefixLocalAt_zero (P : FeedbackEW ι m) (default : ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) : P.PrefixLocalAt default F loss loss' n 0 := by
  intro t ht a hobs
  simp only [executionPrefixMass, AdaptiveEW.execution, FiniteProcess.law]

theorem prefixLocalAt_succ (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent)
    (default : ι) (F : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ)
    (ih : P.PrefixLocalAt default F loss loss' n B) :
    P.PrefixLocalAt default F loss loss' n (B+1) :=
  executionPrefixMass_eq_of_observations_succ P hMeta default F loss loss' n B ih

theorem executionPrefixMass_eq_of_observations (P : FeedbackEW ι m)
    (hMeta : P.MetadataIndependent) (default : ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B)
    (a : ExecutionHistory ι m n B)
    (hobs : ∀ s, s+1 < t → comparisonObservation F (executionPath default n B a s) (loss s) =
      comparisonObservation F (executionPath default n B a s) (loss' s)) :
    P.executionPrefixMass default F loss n B t a =
      P.executionPrefixMass default F loss' n B t a :=
  (Nat.rec (motive := P.PrefixLocalAt default F loss loss' n)
    (prefixLocalAt_zero P default F loss loss' n)
    (fun b ih ↦ prefixLocalAt_succ P hMeta default F loss loss' n b ih) B) t ht a hobs

end
end Tournament.Model.FeedbackEW
