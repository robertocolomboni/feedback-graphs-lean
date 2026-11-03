module

public import Tournament.Probability.FinitePath
public import Tournament.Probability.FiniteConditionalMeasure

@[expose] public section

namespace Tournament.FiniteProcess

open scoped BigOperators Classical MeasureTheory
open MeasureTheory

noncomputable section

universe u

abbrev History (Y : ℕ → Type u) : ℕ → Type u
  | 0 => ULift.{u} Unit
  | b+1 => History Y b × Y b

variable {Y : ℕ → Type u} [∀ b, Fintype (Y b)]

instance historyFintype (b : ℕ) : Fintype (History Y b) := by
  induction b with
  | zero => exact inferInstanceAs (Fintype (ULift.{u} Unit))
  | succ b ih =>
    letI : Fintype (History Y b) := ih
    exact inferInstanceAs (Fintype (History Y b × Y b))

def initial : ProbabilityVector (History Y 0) where
  weight _ := 1
  nonneg _ := by norm_num
  sum_eq_one := by simp [History]

def law (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b)) :
    (B : ℕ) → ProbabilityVector (History Y B)
  | 0 => initial
  | B+1 => (law κ B).joint (κ B)

def past (b : ℕ) : (B : ℕ) → b≤B → History Y B → History Y b
  | 0, h => by
    have hb : b=0 := Nat.eq_zero_of_le_zero h
    subst b
    exact id
  | B+1, h => if heq : b=B+1 then
      fun x ↦ cast (congrArg (History Y) heq.symm) x
    else fun x ↦ past b B (by omega) x.1

omit [∀ b, Fintype (Y b)] in
theorem past_self (b : ℕ) (x : History Y b) : past b b le_rfl x=x := by
  cases b <;> simp [past]

omit [∀ b, Fintype (Y b)] in
theorem past_succ (b B : ℕ) (h : b≤B) (x : History Y (B+1)) :
    past b (B+1) (Nat.le_succ_of_le h) x=past b B h x.1 := by
  simp [past,show b≠B+1 by omega]

omit [∀ b, Fintype (Y b)] in
theorem past_comp (a b B : ℕ) (hab : a≤b) (hbB : b≤B) (x : History Y B) :
    past a b hab (past b B hbB x)=past a B (hab.trans hbB) x := by
  induction B with
  | zero =>
    have hb : b=0 := by omega
    have ha : a=0 := by omega
    subst b
    subst a
    simp [past_self]
  | succ B ih =>
    by_cases hb : b=B+1
    · subst b
      rw [past_self]
    · have hb' : b≤B := by omega
      have ha' : a≤B := hab.trans hb'
      rw [past_succ b B hb',past_succ a B ha']
      exact ih hb' x.1

theorem mean_prefix (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b≤B) (f : History Y b → ℝ) :
    (law κ B).mean (fun x ↦ f (past b B h x))=(law κ b).mean f := by
  induction B with
  | zero =>
    have hb : b=0 := by omega
    subst b
    simp only [past_self]
  | succ B ih =>
    by_cases hb : b=B+1
    · subst b
      simp only [past_self]
    · have hb' : b≤B := by omega
      simp only [past_succ b B hb']
      change ((law κ B).joint (κ B)).mean (fun x ↦ f (past b B hb' x.1))=_
      rw [ProbabilityVector.joint_first_mean (law κ B) (κ B) (fun s ↦ f (past b B hb' s))]
      exact ih hb'

theorem fiberSum_joint {b : ℕ} (μ : ProbabilityVector (History Y b))
    (κ : History Y b → ProbabilityVector (Y b)) (f : History Y (b+1) → ℝ)
    (s : History Y b) :
    FiniteConditional.fiberSum (μ.joint κ) Prod.fst f s=
      μ s*(κ s).mean (fun y ↦ f (s,y)) := by
  unfold FiniteConditional.fiberSum ProbabilityVector.joint ProbabilityVector.mean
  rw [Fintype.sum_prod_type]
  simp only
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem fiberMass_joint {b : ℕ} (μ : ProbabilityVector (History Y b))
    (κ : History Y b → ProbabilityVector (Y b)) (s : History Y b) :
    FiniteConditional.fiberMass (μ.joint κ) Prod.fst s=μ s := by
  have h := fiberSum_joint μ κ (fun _ ↦ 1) s
  simpa only [FiniteConditional.fiberSum,FiniteConditional.fiberMass,mul_one,
    ProbabilityVector.mean_const] using h

theorem fiberSum_prefix (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b+1≤B) (f : History Y (b+1) → ℝ) (s : History Y b) :
    FiniteConditional.fiberSum (law κ B) (past b B (by omega))
      (fun x ↦ f (past (b+1) B h x)) s=
        (law κ b) s*(κ b s).mean (fun y ↦ f (s,y)) := by
  have hp (x : History Y B) :
      (past (b+1) B h x).1=past b B (by omega) x := by
    have hc := past_comp b (b+1) B (by omega) h x
    simpa only [past_succ b b le_rfl,past_self] using hc
  have hmean : FiniteConditional.fiberSum (law κ B) (past b B (by omega))
      (fun x ↦ f (past (b+1) B h x)) s=
      (law κ B).mean (fun x ↦ if past b B (by omega) x=s then
        f (past (b+1) B h x) else 0) := by
    simp only [FiniteConditional.fiberSum,ProbabilityVector.mean,mul_ite,mul_zero]
  rw [hmean]
  calc
    _ = (law κ B).mean (fun x ↦ if (past (b+1) B h x).1=s then
        f (past (b+1) B h x) else 0) := by
      congr 1
      funext x
      rw [hp]
    _ = (law κ (b+1)).mean (fun x ↦ if x.1=s then f x else 0) :=
      mean_prefix κ (b+1) B h (fun x ↦ if x.1=s then f x else 0)
    _ = _ := by
      calc
        _ = FiniteConditional.fiberSum ((law κ b).joint (κ b)) Prod.fst f s := by
          rw [law]
          unfold FiniteConditional.fiberSum ProbabilityVector.mean
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x.1=s <;> simp [hx]
        _ = _ := fiberSum_joint (law κ b) (κ b) f s

theorem fiberMass_prefix (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b≤B) (s : History Y b) :
    FiniteConditional.fiberMass (law κ B) (past b B h) s=(law κ b) s := by
  have hmean : FiniteConditional.fiberMass (law κ B) (past b B h) s=
      (law κ B).mean (fun x ↦ if past b B h x=s then 1 else 0) := by
    simp only [FiniteConditional.fiberMass,ProbabilityVector.mean,mul_ite,mul_one,mul_zero]
  rw [hmean]
  rw [mean_prefix κ b B h (fun x ↦ if x=s then 1 else 0)]
  simp [ProbabilityVector.mean]

end
end Tournament.FiniteProcess
