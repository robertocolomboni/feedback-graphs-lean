module

public import Tournament.Model.ComparisonLocality
public import Tournament.Probability.TrajectoryEncoding
public import Tournament.Upper.BlockPolicy

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical
open FinitePath Upper

noncomputable section

variable {ι : Type*}

def SameActionPrefix (t : ℕ) (a b : ℕ → ι) : Prop := ∀ s < t, a s = b s

theorem sameActionPrefix_append_le (h t : ℕ) (ht : t ≤ h)
    (a b c d : ℕ → ι) :
    SameActionPrefix t (appendActions h a b) (appendActions h c d) ↔
      SameActionPrefix t a c := by
  unfold SameActionPrefix
  constructor <;> intro hp s hs
  · simpa only [appendActions, ite_eq_left (by omega : s < h)] using hp s hs
  · simpa only [appendActions, ite_eq_left (by omega : s < h)] using hp s hs

theorem sameActionPrefix_append_ge (h t : ℕ) (ht : h ≤ t)
    (a b c d : ℕ → ι) :
    SameActionPrefix t (appendActions h a b) (appendActions h c d) ↔
      SameActionPrefix h a c ∧ SameActionPrefix (t-h) b d := by
  constructor
  · intro hp
    constructor
    · intro s hs
      simpa only [appendActions, ite_eq_left hs] using hp s (by omega)
    · intro s hs
      simpa only [appendActions, ite_eq_right (by omega : ¬ h+s < h),
        Nat.add_sub_cancel_left] using hp (h+s) (by omega)
  · rintro ⟨ha,hb⟩ s hs
    by_cases hsh : s < h
    · simpa only [appendActions, ite_eq_left hsh] using ha s hsh
    · simpa only [appendActions, ite_eq_right hsh] using hb (s-h) (by omega)

theorem path_sameActionPrefix_iff (n k : ℕ) (hk : k ≤ n)
    (a b : History ι n) :
    SameActionPrefix (k+1) (stateAt n a) (stateAt n b) ↔
      initialSegment n a k hk = initialSegment n b k hk := by
  constructor
  · intro hp
    apply (traceEquiv k).injective
    funext i
    change trace k (initialSegment n a k hk) i = trace k (initialSegment n b k hk) i
    rw [trace_eq_stateAt, trace_eq_stateAt,
      stateAt_initialSegment n a k i.val hk (by omega),
      stateAt_initialSegment n b k i.val hk (by omega)]
    exact hp i.val i.isLt
  · intro heq s hs
    rw [← stateAt_initialSegment n a k s hk (by omega),
      ← stateAt_initialSegment n b k s hk (by omega), heq]

theorem path_sameActionPrefix_full (n : ℕ) (a b : History ι n) :
    SameActionPrefix (n+1) (stateAt n a) (stateAt n b) ↔ a = b := by
  rw [path_sameActionPrefix_iff n n le_rfl, prefix_self, prefix_self]

variable [Fintype ι]

theorem ComparisonPolicy.mean_prefix_indicator (π : ComparisonPolicy ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n k : ℕ) (hk : k ≤ n)
    (a : History ι n) :
    (π.law F loss n).mean
      (fun x ↦ if SameActionPrefix (k+1) (stateAt n x) (stateAt n a) then 1 else 0) =
      π.law F loss k (initialSegment n a k hk) := by
  simp_rw [path_sameActionPrefix_iff n k hk]
  have h := π.mean_prefix F loss n k hk
    (fun x ↦ if x = initialSegment n a k hk then 1 else 0)
  simpa [ProbabilityVector.mean, mul_ite] using h

namespace ResetComparisonPolicy

def prefixMass (π : ResetComparisonPolicy ι) (default : ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) (t : ℕ)
    (a : BlockOutcome ι ns) : ℝ :=
  (π.law F loss offset ns).mean
    (fun x ↦ if SameActionPrefix t (blockActions default ns x)
      (blockActions default ns a) then 1 else 0)

theorem prefixMass_zero (π : ResetComparisonPolicy ι) (default : ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) (a : BlockOutcome ι ns) :
    π.prefixMass default F loss offset ns 0 a = 1 := by
  simp only [prefixMass, SameActionPrefix, Nat.not_lt_zero, IsEmpty.forall_iff,
    implies_true, ite_true, ProbabilityVector.mean_const]

theorem prefixMass_in_head (π : ResetComparisonPolicy ι) (default : ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) (ns : List ℕ) (k : ℕ) (hk : k ≤ n)
    (a : BlockOutcome ι (n::ns)) :
    π.prefixMass default F loss offset (n::ns) (k+1) a =
      (π.chunk offset n).law F (fun s ↦ loss (offset+s)) k
        (initialSegment n a.1 k hk) := by
  unfold prefixMass
  change (((π.chunk offset n).law F (fun s ↦ loss (offset+s)) n).joint
    (fun _ ↦ π.law F loss (offset+(n+1)) ns)).mean _ = _
  simp_rw [blockActions, sameActionPrefix_append_le (n+1) (k+1) (by omega)]
  rw [ProbabilityVector.joint_first_mean
    ((π.chunk offset n).law F (fun s ↦ loss (offset+s)) n)
    (fun _ ↦ π.law F loss (offset+(n+1)) ns)
    (fun x ↦ if SameActionPrefix (k+1) (stateAt n x) (stateAt n a.1) then 1 else 0)]
  exact ComparisonPolicy.mean_prefix_indicator _ _ _ n k hk a.1

theorem prefixMass_after_head (π : ResetComparisonPolicy ι) (default : ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) (ns : List ℕ) (t : ℕ) (ht : n+1 ≤ t)
    (a : BlockOutcome ι (n::ns)) :
    π.prefixMass default F loss offset (n::ns) t a =
      (π.chunk offset n).law F (fun s ↦ loss (offset+s)) n a.1 *
        π.prefixMass default F loss (offset+(n+1)) ns (t-(n+1)) a.2 := by
  unfold prefixMass
  change (((π.chunk offset n).law F (fun s ↦ loss (offset+s)) n).joint
    (fun _ ↦ π.law F loss (offset+(n+1)) ns)).mean _ = _
  simp_rw [blockActions, sameActionPrefix_append_ge (n+1) t ht,
    path_sameActionPrefix_full]
  rw [ProbabilityVector.joint_mean]
  simp [ProbabilityVector.mean, mul_ite, ite_and]

theorem prefixMass_eq_of_observations (π : ResetComparisonPolicy ι)
    (default : ι) (F : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ)
    (ns : List ℕ) (offset t : ℕ) (ht : t ≤ Restarts.totalRounds ns)
    (a : BlockOutcome ι ns)
    (hobs : ∀ s, s+1 < t → comparisonObservation F (blockActions default ns a s)
      (loss (offset+s)) = comparisonObservation F (blockActions default ns a s)
      (loss' (offset+s))) :
    π.prefixMass default F loss offset ns t a =
      π.prefixMass default F loss' offset ns t a := by
  induction ns generalizing offset t with
  | nil =>
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    rw [prefixMass_zero, prefixMass_zero]
  | cons n ns ih =>
    by_cases ht0 : t = 0
    · subst t
      rw [prefixMass_zero, prefixMass_zero]
    · by_cases htn : t ≤ n+1
      · have heq : t = (t-1)+1 := by omega
        have hk : t-1 ≤ n := by omega
        rw [heq, prefixMass_in_head π default F loss offset n ns (t-1) hk,
          prefixMass_in_head π default F loss' offset n ns (t-1) hk]
        apply ComparisonPolicy.law_atom_eq_of_observations
        intro s hs
        rw [stateAt_initialSegment n a.1 (t-1) s hk (by omega)]
        have ho := hobs s (by omega)
        simpa only [blockActions, appendActions, ite_eq_left (by omega : s < n+1)] using ho
      · have hnt : n+1 ≤ t := by omega
        rw [prefixMass_after_head π default F loss offset n ns t hnt,
          prefixMass_after_head π default F loss' offset n ns t hnt]
        congr 1
        · apply ComparisonPolicy.law_atom_eq_of_observations
          intro s hs
          have ho := hobs s (by omega)
          simpa only [blockActions, appendActions, ite_eq_left (by omega : s < n+1)] using ho
        · apply ih (offset+(n+1)) (t-(n+1))
          · change t ≤ (n+1)+Restarts.totalRounds ns at ht
            omega
          · intro s hs
            have ho := hobs (n+1+s) (by omega)
            simp only [blockActions, appendActions,
              ite_eq_right (by omega : ¬ n+1+s < n+1), Nat.add_sub_cancel_left] at ho
            simpa only [Nat.add_assoc] using ho

end ResetComparisonPolicy
end
end Tournament.Model
