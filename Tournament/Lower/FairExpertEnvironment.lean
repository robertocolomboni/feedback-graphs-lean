module

public import Tournament.Lower.FairSignAbsolute
public import Tournament.Model.Minimax
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Tournament.Lower.FairExperts

open MeasureTheory Model MeasurableGame
open scoped Classical BigOperators
noncomputable section

variable {ι : Type*} {T : ℕ}

def signAt (t : ℕ) (ω : FairSigns.Space T) : ℝ :=
  if ht : t<T then FairSigns.sign ⟨t,ht⟩ ω else 0

theorem signAt_bounds (t : ℕ) (ω : FairSigns.Space T) : -1≤signAt t ω ∧ signAt t ω≤1 := by
  unfold signAt
  split_ifs
  · exact abs_le.mp (le_of_eq (FairSigns.value_abs _))
  · constructor <;> norm_num

def loss (a b : ι) (t : ℕ) (ω : FairSigns.Space T) (i : ι) : ℝ :=
  if i=a then (1+signAt t ω)/2 else if i=b then (1-signAt t ω)/2 else 1

theorem loss_bounds (a b : ι) (t : ℕ) (ω : FairSigns.Space T) (i : ι) :
    0≤loss a b t ω i ∧ loss a b t ω i≤1 := by
  have h := signAt_bounds t ω
  unfold loss
  split_ifs <;> constructor <;> linarith

theorem loss_measurable (a b : ι) (t : ℕ) : Measurable (loss (T := T) a b t) := Measurable.of_discrete

def coefficient (a b i : ι) : ℝ := if i=a then 1 else if i=b then -1 else 0

theorem selected_loss_lower (a b i : ι) (t : ℕ) (ω : FairSigns.Space T) :
    1/2+signAt t ω*coefficient a b i/2≤loss a b t ω i := by
  unfold loss coefficient
  split_ifs <;> linarith

theorem coefficient_abs_le (a b i : ι) : |coefficient a b i|≤1 := by
  unfold coefficient
  split_ifs <;> norm_num

theorem signAt_sum (ω : FairSigns.Space T) :
    (∑ t∈Finset.range T, signAt t ω)=∑ t : Fin T, FairSigns.sign t ω := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t _
  simp only [signAt,dite_eq_left t.isLt]

variable [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem fixedLoss_first (a b : ι) (ω : FairSigns.Space T) :
    fixedLoss T (fun t ↦ loss a b t ω) a=((T:ℝ)+∑ t : Fin T, FairSigns.sign t ω)/2 := by
  simp only [fixedLoss]
  simp [loss,← Finset.sum_div,Finset.sum_add_distrib,signAt_sum]

omit [Fintype ι] [Nonempty ι] in
theorem fixedLoss_second (a b : ι) (hab : a≠b) (ω : FairSigns.Space T) :
    fixedLoss T (fun t ↦ loss a b t ω) b=((T:ℝ)-∑ t : Fin T, FairSigns.sign t ω)/2 := by
  simp only [fixedLoss]
  simp [loss,hab.symm,← Finset.sum_div,Finset.sum_sub_distrib,signAt_sum]

theorem bestFixedLoss_upper (a b : ι) (hab : a≠b) (ω : FairSigns.Space T) :
    bestFixedLoss T (fun t ↦ loss a b t ω)≤(T:ℝ)/2-|∑ t : Fin T, FairSigns.sign t ω|/2 := by
  have hA := bestFixedLoss_le T (fun t ↦ loss a b t ω) a
  have hB := bestFixedLoss_le T (fun t ↦ loss a b t ω) b
  rw [fixedLoss_first] at hA
  rw [fixedLoss_second a b hab] at hB
  rcases le_total (∑ t : Fin T, FairSigns.sign t ω) 0 with h | h
  · rw [abs_of_nonpos h]
    linarith
  · rw [abs_of_nonneg h]
    linarith

omit [Fintype ι] [Nonempty ι] in
theorem loss_past_flip (a b : ι) (t : Fin T) (s : ℕ) (hst : s<t.val) (ω : FairSigns.Space T) :
    loss a b s (FairSigns.flip t ω)=loss a b s ω := by
  have hs : s<T := hst.trans t.isLt
  have hne : (⟨s,hs⟩ : Fin T)≠t := by
    intro h
    have hv := congrArg Fin.val h
    change s=t.val at hv
    omega
  funext i
  simp only [loss,signAt,dite_eq_left hs,FairSigns.sign_flip_other t ⟨s,hs⟩ hne]

variable {Seed : Type*} [MeasurableSpace ι] [MeasurableSpace Seed]

def learnerAction (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (s : ℕ) :
    Seed × FairSigns.Space T → ι := action π E (loss a b) s

omit [Fintype ι] [Nonempty ι] in
theorem learnerAction_flip (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι)
    (t : Fin T) (seed : Seed) (ω : FairSigns.Space T) :
    learnerAction π E a b t.val (seed,FairSigns.flip t ω)=learnerAction π E a b t.val (seed,ω) := by
  symm
  apply action_equal_of_past_feedback π E (loss a b) (loss a b) t.val (seed,ω) (seed,FairSigns.flip t ω) rfl
  intro s hs
  rw [loss_past_flip a b t s hs ω]

end
end Tournament.Lower.FairExperts
