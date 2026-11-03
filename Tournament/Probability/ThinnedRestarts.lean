module

public import Tournament.Probability.ChunkMembership
public import Tournament.Probability.ChronologicalPath
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace Tournament.Restarts

open scoped BigOperators Classical

noncomputable section

def thin : (n : ℕ) → Coins n → Coins n → Coins n
  | 0, _, _ => ()
  | n+1, (cut,rest), (keep,tail) => (cut && keep,thin n rest tail)

theorem zero_mean {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (f : Coins 0 → ℝ) :
    (law τ hτ hτ1 0).mean f=f () := by
  change (∑ x : Unit, (1:ℝ)*f x)=f ()
  simp

theorem thin_mean {τ q : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hprod : τ*q ≤ 1) : ∀ n (f : Coins n → ℝ),
    (law τ hτ hτ1 n).mean (fun cuts ↦ (law q hq hq1 n).mean (fun keep ↦ f (thin n cuts keep))) =
      (law (τ*q) (mul_nonneg hτ hq) hprod n).mean f := by
  intro n
  induction n with
  | zero => intro f; rw [zero_mean,zero_mean,zero_mean]
  | succ n ih =>
    intro f
    have hstep : ∀ cut : Bool,
        (law τ hτ hτ1 n).mean (fun rest ↦ (law q hq hq1 (n+1)).mean
          (fun keep ↦ f (thin (n+1) (cut,rest) keep))) =
        q*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (cut && true,tail))+
          (1-q)*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (cut && false,tail)) := by
      intro cut
      have hfun : (fun rest : Coins n ↦ (law q hq hq1 (n+1)).mean
          (fun keep ↦ f (thin (n+1) (cut,rest) keep))) =
          (fun rest ↦ q*(law q hq hq1 n).mean (fun tail ↦ f (cut && true,thin n rest tail))+
            (1-q)*(law q hq hq1 n).mean (fun tail ↦ f (cut && false,thin n rest tail))) := by
        funext rest
        change ((coin q hq hq1).joint (fun _ ↦ law q hq hq1 n)).mean
          (fun keep : Bool × Coins n ↦ f (thin (n+1) (cut,rest) keep)) = _
        rw [ProbabilityVector.joint_mean,coin_mean]
        rfl
      rw [hfun,ProbabilityVector.mean_add,ProbabilityVector.mean_const_mul,
        ProbabilityVector.mean_const_mul,ih (fun tail ↦ f (cut && true,tail)),
        ih (fun tail ↦ f (cut && false,tail))]
    change ((coin τ hτ hτ1).joint (fun _ ↦ law τ hτ hτ1 n)).mean
      (fun cuts : Bool × Coins n ↦ (law q hq hq1 (n+1)).mean (fun keep ↦ f (thin (n+1) cuts keep))) = _
    rw [ProbabilityVector.joint_mean,coin_mean,hstep true,hstep false]
    simp only [Bool.and_true,Bool.and_false]
    change τ*(q*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (true,tail))+
        (1-q)*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (false,tail)))+
      (1-τ)*(q*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (false,tail))+
        (1-q)*(law (τ*q) (mul_nonneg hτ hq) hprod n).mean (fun tail ↦ f (false,tail))) =
      ((coin (τ*q) (mul_nonneg hτ hq) hprod).joint (fun _ ↦ law (τ*q) (mul_nonneg hτ hq) hprod n)).mean f
    rw [ProbabilityVector.joint_mean,coin_mean]
    ring

theorem thin_noRestart_self {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) (cuts : Coins n) (i : ℕ) :
    (law q hq hq1 n).probability (fun keep ↦ noRestart n (thin n cuts keep) i i) =
      (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) i)) := by
  unfold ProbabilityVector.probability
  have heq : (fun keep : Coins n ↦ if noRestart n (thin n cuts keep) i i then (1:ℝ) else 0) = (fun _ ↦ 1) := by
    funext keep
    rw [ite_eq_left (noRestart_self n (thin n cuts keep) i)]
  rw [heq,ProbabilityVector.mean_const,Nat.dist_self,pow_zero]

theorem thin_noRestart_probability {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) (cuts : Coins n) (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (law q hq hq1 n).probability (fun keep ↦ noRestart n (thin n cuts keep) i j) =
      (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j)) := by
  induction n generalizing i j with
  | zero =>
    have hj0 : j=0 := by omega
    have hi0 : i=0 := by omega
    subst j
    subst i
    exact thin_noRestart_self hq hq1 0 cuts 0
  | succ n ih =>
    rcases cuts with ⟨cut,rest⟩
    cases j with
    | zero =>
      have hi0 : i=0 := by omega
      subst i
      exact thin_noRestart_self hq hq1 (n+1) (cut,rest) 0
    | succ j =>
      cases i with
      | zero =>
        unfold ProbabilityVector.probability
        change ((coin q hq hq1).joint (fun _ ↦ law q hq hq1 n)).mean
          (fun keep : Bool × Coins n ↦ if noRestart (n+1) (thin (n+1) (cut,rest) keep) 0 (j+1) then 1 else 0) = _
        rw [ProbabilityVector.joint_mean,coin_mean]
        have hfalse : (fun tail : Coins n ↦
            if noRestart (n+1) (thin (n+1) (cut,rest) (false,tail)) 0 (j+1) then (1:ℝ) else 0) =
            (fun tail ↦ if noRestart n (thin n rest tail) 0 j then 1 else 0) := by
          funext tail
          simp only [thin,Bool.and_false,noRestart_zero_succ,true_and]
        rw [hfalse]
        have hi := ih rest 0 j (Nat.zero_le j) (by omega)
        cases cut with
        | true =>
          have htrue : (fun tail : Coins n ↦
              if noRestart (n+1) (thin (n+1) (true,rest) (true,tail)) 0 (j+1) then (1:ℝ) else 0) =
              (fun _ ↦ 0) := by
            funext tail
            simp [thin,noRestart_zero_succ]
          rw [htrue,ProbabilityVector.mean_const,mul_zero,zero_add]
          change (1-q)*(law q hq hq1 n).probability (fun tail ↦ noRestart n (thin n rest tail) 0 j) = _
          rw [hi]
          simp only [chunkIndex_parts_zero,chunkIndex_parts_succ,ite_true,Nat.dist_zero_left,pow_add,pow_one]
        | false =>
          have htrue : (fun tail : Coins n ↦
              if noRestart (n+1) (thin (n+1) (false,rest) (true,tail)) 0 (j+1) then (1:ℝ) else 0) =
              (fun tail ↦ if noRestart n (thin n rest tail) 0 j then 1 else 0) := by
            funext tail
            simp only [thin,Bool.and_true,noRestart_zero_succ,true_and]
          rw [htrue]
          change q*(law q hq hq1 n).probability (fun tail ↦ noRestart n (thin n rest tail) 0 j)+
            (1-q)*(law q hq hq1 n).probability (fun tail ↦ noRestart n (thin n rest tail) 0 j) = _
          rw [hi,chunkIndex_parts_zero,chunkIndex_parts_succ]
          simp only [Bool.false_eq_true,ite_false,Nat.dist_zero_left]
          rw [chunkIndex_parts_zero,Nat.dist_zero_left]
          ring
      | succ i =>
        unfold ProbabilityVector.probability
        change ((coin q hq hq1).joint (fun _ ↦ law q hq hq1 n)).mean
          (fun keep : Bool × Coins n ↦ if noRestart (n+1) (thin (n+1) (cut,rest) keep) (i+1) (j+1) then 1 else 0) = _
        have heq : (fun keep : Bool × Coins n ↦
            if noRestart (n+1) (thin (n+1) (cut,rest) keep) (i+1) (j+1) then (1:ℝ) else 0) =
            (fun keep ↦ if noRestart n (thin n rest keep.2) i j then 1 else 0) := by
          funext keep
          rcases keep with ⟨head,tail⟩
          simp only [thin,noRestart_succ_succ]
        rw [heq,ProbabilityVector.joint_mean]
        change (coin q hq hq1).mean (fun _ ↦ (law q hq hq1 n).probability
          (fun tail ↦ noRestart n (thin n rest tail) i j)) = _
        rw [ProbabilityVector.mean_const,ih rest i j (by omega) (by omega),
          chunkIndex_parts_succ,chunkIndex_parts_succ]
        cases cut <;> simp [Nat.dist_add_add_left]

theorem intervalDistance_generating_ordered {τ q : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hprod : τ*q ≤ 1)
    (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (law τ hτ hτ1 n).mean (fun cuts ↦
      (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j))) =
        (1-τ*q)^(j-i) := by
  have ht := thin_mean hτ hτ1 hq hq1 hprod n (fun coarse ↦ if noRestart n coarse i j then (1:ℝ) else 0)
  have hinner : (fun cuts : Coins n ↦ (law q hq hq1 n).mean
      (fun keep ↦ if noRestart n (thin n cuts keep) i j then (1:ℝ) else 0)) =
      (fun cuts ↦ (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j))) := by
    funext cuts
    exact thin_noRestart_probability hq hq1 n cuts i j hij hjn
  rw [hinner] at ht
  change (law τ hτ hτ1 n).mean (fun cuts ↦
    (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j))) =
      (law (τ*q) (mul_nonneg hτ hq) hprod n).probability (fun coarse ↦ noRestart n coarse i j) at ht
  rw [noRestart_probability (mul_nonneg hτ hq) hprod n i j hij hjn] at ht
  exact ht

theorem intervalDistance_generating {τ q : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hprod : τ*q ≤ 1)
    (n i j : ℕ) (hin : i ≤ n) (hjn : j ≤ n) :
    (law τ hτ hτ1 n).mean (fun cuts ↦
      (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j))) =
        (1-τ*q)^(Nat.dist i j) := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    exact intervalDistance_generating_ordered hτ hτ1 hq hq1 hprod n i j hij hjn
  · have h := intervalDistance_generating_ordered hτ hτ1 hq hq1 hprod n j i hji hin
    have heq : (fun cuts : Coins n ↦
        (1-q)^(Nat.dist (chunkIndex (parts n cuts) i) (chunkIndex (parts n cuts) j))) =
        (fun cuts ↦ (1-q)^(Nat.dist (chunkIndex (parts n cuts) j) (chunkIndex (parts n cuts) i))) := by
      funext cuts
      rw [Nat.dist_comm]
    rw [heq,Nat.dist_eq_sub_of_le_right hji]
    exact h

end
end Tournament.Restarts
