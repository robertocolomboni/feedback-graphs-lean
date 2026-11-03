module

public import Tournament.Probability.FiniteKernel
public import Tournament.Upper.HoldingFamily
public import Tournament.Model.Regret
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament

open scoped BigOperators

namespace ProbabilityVector

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def joint (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector ι) :
    ProbabilityVector (Ω × ι) where
  weight x := μ x.1 * κ x.1 x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((κ x.1).nonneg x.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ProbabilityVector.sum_eq_one, mul_one]
    exact μ.sum_eq_one

theorem joint_mean (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector ι)
    (f : Ω × ι → ℝ) :
    (μ.joint κ).mean f = μ.mean (fun x ↦ (κ x).mean (fun y ↦ f (x,y))) := by
  unfold mean joint
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem joint_first_mean (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector ι)
    (f : Ω → ℝ) :
    (μ.joint κ).mean (fun x ↦ f x.1) = μ.mean f := by
  rw [joint_mean]
  simp only [mean_const]

theorem joint_prefix_weight (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector ι) (x : Ω) :
    (∑ y, μ.joint κ (x,y)) = μ x := by
  change (∑ y, μ x * κ x y) = μ x
  rw [← Finset.mul_sum, (κ x).sum_eq_one, mul_one]

theorem joint_next_given_prefix (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector ι)
    (x : Ω) (y : ι) (hx : 0 < μ x) :
    μ.joint κ (x,y) / (∑ z, μ.joint κ (x,z)) = κ x y := by
  rw [joint_prefix_weight]
  change μ x * κ x y / μ x = κ x y
  field_simp [ne_of_gt hx]

end ProbabilityVector

namespace FinitePath

variable {ι : Type*} [Fintype ι]

abbrev History (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n+1 => History ι n × ι

instance historyFintype (n : ℕ) : Fintype (History ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype ι)
  | succ n ih =>
    letI : Fintype (History ι n) := ih
    change Fintype (History ι n × ι)
    infer_instance

def lastState : (n : ℕ) → History ι n → ι
  | 0, i => i
  | _+1, (_,i) => i

def stateAt : (n : ℕ) → History ι n → ℕ → ι
  | 0, i, _ => i
  | n+1, (hist,i), t => if t ≤ n then stateAt n hist t else i

omit [Fintype ι] in
theorem stateAt_last (n : ℕ) (hist : History ι n) :
    stateAt n hist n = lastState n hist := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases hist with ⟨hist,i⟩
    simp [stateAt, lastState]

omit [Fintype ι] in
theorem stateAt_prefix (n : ℕ) (hist : History ι n × ι) (t : ℕ) (ht : t ≤ n) :
    stateAt (n+1) hist t = stateAt n hist.1 t := by
  simp [stateAt, ht]

def law (P : FiniteKernel ι) (p : ProbabilityVector ι) :
    (n : ℕ) → ProbabilityVector (History ι n)
  | 0 => p
  | n+1 => (law P p n).joint (fun hist ↦ P.row (lastState n hist))

theorem stationary_latest_mean (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Stationary p) (n : ℕ) (f : ι → ℝ) :
    (law P p n).mean (fun hist ↦ f (lastState n hist)) = p.mean f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean
      (fun hist ↦ f hist.2) = p.mean f
    rw [ProbabilityVector.joint_mean]
    change (law P p n).mean (fun hist ↦ (P.act f) (lastState n hist)) = p.mean f
    rw [ih (P.act f), P.stationary_mean_act p h f]

theorem stationary_latest_probability [DecidableEq ι] (P : FiniteKernel ι)
    (p : ProbabilityVector ι) (h : P.Stationary p) (n : ℕ) (i : ι) :
    (law P p n).mean (fun hist ↦ if lastState n hist = i then 1 else 0) = p i := by
  simpa [ProbabilityVector.mean] using
    (stationary_latest_mean P p h n (fun j ↦ if j=i then (1:ℝ) else 0))

theorem stationary_stateAt_mean (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Stationary p) (n t : ℕ) (ht : t ≤ n) (f : ι → ℝ) :
    (law P p n).mean (fun hist ↦ f (stateAt n hist t)) = p.mean f := by
  induction n generalizing t with
  | zero =>
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    rfl
  | succ n ih =>
    by_cases htn : t ≤ n
    · change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist ↦ f (stateAt (n+1) hist t)) = _
      have heq : (fun hist : History ι n × ι ↦ f (stateAt (n+1) hist t)) =
          (fun hist ↦ f (stateAt n hist.1 t)) := by
        funext hist
        rw [stateAt_prefix n hist t htn]
      rw [heq, ProbabilityVector.joint_first_mean (law P p n)
        (fun hist ↦ P.row (lastState n hist)) (fun hist ↦ f (stateAt n hist t))]
      exact ih t htn
    · have ht' : t = n+1 := le_antisymm ht (Nat.succ_le_of_lt (lt_of_not_ge htn))
      subst t
      simpa only [stateAt_last] using stationary_latest_mean P p h (n+1) f

def switches [DecidableEq ι] : (n : ℕ) → History ι n → ℕ
  | 0, _ => 0
  | n+1, (hist,i) => switches n hist + (if i = lastState n hist then 0 else 1)

omit [Fintype ι] in

theorem switches_eq_switchCount [DecidableEq ι] (n : ℕ) (hist : History ι n) :
    switches n hist = Model.switchCount (n+1) (stateAt n hist) := by
  induction n with
  | zero => simp [switches, Model.switchCount]
  | succ n ih =>
    change switches n hist.1 + (if hist.2=lastState n hist.1 then 0 else 1) =
      ∑ t ∈ Finset.range (n+1),
        if stateAt (n+1) hist (t+1)=stateAt (n+1) hist t then 0 else 1
    rw [Finset.sum_range_succ]
    have hprefix : (∑ t ∈ Finset.range n,
        if stateAt (n+1) hist (t+1)=stateAt (n+1) hist t then 0 else 1) =
        Model.switchCount (n+1) (stateAt n hist.1) := by
      change _ = ∑ t ∈ Finset.range n,
        if stateAt n hist.1 (t+1)=stateAt n hist.1 t then 0 else 1
      apply Finset.sum_congr rfl
      intro t ht
      have htn : t < n := Finset.mem_range.mp ht
      rw [stateAt_prefix n hist (t+1) (Nat.succ_le_of_lt htn),
        stateAt_prefix n hist t (Nat.le_of_lt htn)]
    have hlast : (if stateAt (n+1) hist (n+1)=stateAt (n+1) hist n then 0 else 1) =
        (if hist.2=lastState n hist.1 then 0 else 1) := by
      rw [stateAt_last, stateAt_prefix n hist n le_rfl, stateAt_last]
      rfl
    rw [hprefix, hlast, ih hist.1]

theorem expected_switches_step [DecidableEq ι] (P : FiniteKernel ι)
    (p : ProbabilityVector ι) (h : P.Stationary p) (n : ℕ) :
    (law P p (n+1)).mean (fun hist ↦ (switches (n+1) hist : ℝ)) =
      (law P p n).mean (fun hist ↦ (switches n hist : ℝ)) +
        p.mean (fun i ↦ 1 - P i i) := by
  change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean
    (fun hist ↦ (switches n hist.1 + (if hist.2=lastState n hist.1 then 0 else 1) : ℕ)) = _
  have hf : (fun hist : History ι n × ι ↦
      ((switches n hist.1 + (if hist.2=lastState n hist.1 then 0 else 1) : ℕ) : ℝ)) =
      (fun hist ↦ (switches n hist.1 : ℝ) + (if hist.2=lastState n hist.1 then 0 else 1)) := by
    funext hist
    split <;> simp
  rw [hf, ProbabilityVector.mean_add,
    ProbabilityVector.joint_first_mean (law P p n) (fun hist ↦ P.row (lastState n hist))
      (fun hist ↦ (switches n hist : ℝ)),
    ProbabilityVector.joint_mean]
  congr 1
  have heq : (fun hist : History ι n ↦
      (P.row (lastState n hist)).mean (fun i ↦ if i=lastState n hist then 0 else 1)) =
      (fun hist ↦ 1 - P (lastState n hist) (lastState n hist)) := by
    funext hist
    exact P.row_switch_probability (lastState n hist)
  rw [heq]
  exact stationary_latest_mean P p h n (fun i ↦ 1 - P i i)

theorem expected_switches [DecidableEq ι] (P : FiniteKernel ι)
    (p : ProbabilityVector ι) (h : P.Stationary p) (n : ℕ) :
    (law P p n).mean (fun hist ↦ (switches n hist : ℝ)) =
      n * p.mean (fun i ↦ 1 - P i i) := by
  induction n with
  | zero => simp [switches, ProbabilityVector.mean]
  | succ n ih =>
    rw [expected_switches_step P p h n, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem holding_expected_switches [DecidableEq ι] (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    (law (H.kernel τ hτ) H.sampling n).mean (fun hist ↦ (switches n hist : ℝ)) ≤
      n * τ / 2 := by
  rw [expected_switches _ _ (H.kernel_stationary hτ) n]
  have hmean : H.sampling.mean (fun i ↦ 1 - H.kernel τ hτ i i) ≤ τ / 2 := by
    calc
      H.sampling.mean (fun i ↦ 1 - H.kernel τ hτ i i) ≤
          H.sampling.mean (H.refreshRate τ) := by
        apply H.sampling.mean_mono
        intro i
        have hi := H.kernel_holding_lower hτ i
        linarith
      _ = H.meanRefreshRate τ := rfl
      _ ≤ τ / 2 := H.meanRefreshRate_le (le_of_lt hτ)
  calc
    (n:ℝ) * H.sampling.mean (fun i ↦ 1 - H.kernel τ hτ i i) ≤ n * (τ / 2) :=
      mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg n)
    _ = n * τ / 2 := by ring

theorem holding_expected_switchCount [DecidableEq ι] (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    (law (H.kernel τ hτ) H.sampling n).mean
      (fun hist ↦ (Model.switchCount (n+1) (stateAt n hist) : ℝ)) ≤ n * τ / 2 := by
  have heq : (fun hist : History ι n ↦
      (Model.switchCount (n+1) (stateAt n hist) : ℝ)) =
      (fun hist ↦ (switches n hist : ℝ)) := by
    funext hist
    rw [switches_eq_switchCount]
  rw [heq]
  exact holding_expected_switches H hτ n

theorem holding_expected_switchCount_horizon [DecidableEq ι] (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (h : ℕ) (hh : 1 ≤ h) :
    (law (H.kernel τ hτ) H.sampling (h-1)).mean
      (fun hist ↦ (Model.switchCount h (stateAt (h-1) hist) : ℝ)) ≤ (h-1:ℕ) * τ / 2 := by
  simpa only [Nat.sub_add_cancel hh] using holding_expected_switchCount H hτ (h-1)

end FinitePath
end Tournament
