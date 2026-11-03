module

public import Tournament.Graphs.Domination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.ObserverThinning

open scoped Classical BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def Heavy (E : ι → ι → Prop) (f : ℝ) (W : Finset ι) (a : ι) : Prop :=
  f*(W.card:ℝ)<((observedMembers E W a).card:ℝ)

def step (E : ι → ι → Prop) (f : ℝ) (s : Finset ι × Finset ι) : Finset ι × Finset ι :=
  if h : ∃ a, Heavy E f s.1 a then
    let a := Classical.choose h
    (s.1 \ observedMembers E s.1 a,insert a s.2)
  else s

def state (E : ι → ι → Prop) (f : ℝ) : ℕ → Finset ι × Finset ι
  | 0 => (Finset.univ,∅)
  | n+1 => step E f (state E f n)

theorem step_selected_card_le (E : ι → ι → Prop) (f : ℝ) (s : Finset ι × Finset ι) :
    (step E f s).2.card≤s.2.card+1 := by
  unfold step
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

theorem selected_card_le (E : ι → ι → Prop) (f : ℝ) (n : ℕ) : (state E f n).2.card≤n := by
  induction n with
  | zero => simp only [state,Finset.card_empty,le_refl]
  | succ n ih => exact (step_selected_card_le E f (state E f n)).trans (Nat.succ_le_succ ih)

theorem step_covers (E : ι → ι → Prop) (f : ℝ) (s : Finset ι × Finset ι)
    (hCover : ∀ v, v∉s.1 → ∃ a∈s.2, E a v) :
    ∀ v, v∉(step E f s).1 → ∃ a∈(step E f s).2, E a v := by
  unfold step
  split_ifs with h
  · intro v hv
    by_cases hvW : v∈s.1
    · have hvO : v∈observedMembers E s.1 (Classical.choose h) := by
        by_contra hn
        exact hv (Finset.mem_sdiff.mpr ⟨hvW,hn⟩)
      exact ⟨Classical.choose h,Finset.mem_insert_self _ _,(Finset.mem_filter.mp hvO).2⟩
    · obtain ⟨a,ha,hav⟩ := hCover v hvW
      exact ⟨a,Finset.mem_insert_of_mem ha,hav⟩
  · exact hCover

theorem covers_removed (E : ι → ι → Prop) (f : ℝ) (n : ℕ) :
    ∀ v, v∉(state E f n).1 → ∃ a∈(state E f n).2, E a v := by
  induction n with
  | zero => intro v hv; exact False.elim (hv (Finset.mem_univ v))
  | succ n ih => exact step_covers E f (state E f n) ih

theorem remainder_nonempty (E : ι → ι → Prop) (hE : Observable E) (f : ℝ) (n : ℕ)
    (hn : n<dominationNumber E hE) : (state E f n).1.Nonempty := by
  by_contra hW
  have hObs : ObservingSet E (state E f n).2 := by
    intro v
    exact covers_removed E f n v (by simp [Finset.not_nonempty_iff_eq_empty.mp hW])
  have hMin := dominationNumber_le E hE (state E f n).2 hObs
  have hCard := selected_card_le E f n
  omega

theorem step_card_lt (E : ι → ι → Prop) (f : ℝ) (s : Finset ι × Finset ι)
    (hHeavy : ∃ a, Heavy E f s.1 a) :
    ((step E f s).1.card:ℝ)<(1-f)*(s.1.card:ℝ) := by
  have hSub : observedMembers E s.1 (Classical.choose hHeavy) ⊆ s.1 := Finset.filter_subset _ _
  unfold step
  rw [dite_eq_left hHeavy,Finset.card_sdiff_of_subset hSub,Nat.cast_sub (Finset.card_le_card hSub)]
  have h := Classical.choose_spec hHeavy
  unfold Heavy at h
  calc
    _ < (s.1.card:ℝ)-f*(s.1.card:ℝ) := sub_lt_sub_left h _
    _ = _ := by ring

theorem remainder_card_le_power (E : ι → ι → Prop) (f : ℝ) (hf : f≤1) (n : ℕ)
    (hHeavy : ∀ t<n, ∃ a, Heavy E f (state E f t).1 a) :
    ((state E f n).1.card:ℝ)≤(Fintype.card ι:ℝ)*(1-f)^n := by
  induction n with
  | zero => simp only [state,Finset.card_univ,pow_zero,mul_one,le_refl]
  | succ n ih =>
    have hStep := step_card_lt E f (state E f n) (hHeavy n (by omega))
    have hPrev := ih (fun t ht ↦ hHeavy t (by omega))
    calc
      _ ≤ (1-f)*((state E f n).1.card:ℝ) := hStep.le
      _ ≤ (1-f)*((Fintype.card ι:ℝ)*(1-f)^n) := mul_le_mul_of_nonneg_left hPrev (by linarith)
      _ = _ := by rw [pow_succ]; ring

theorem remainder_card_lt_power (E : ι → ι → Prop) (f : ℝ) (hf : f≤1) (n : ℕ) (hn : 1≤n)
    (hHeavy : ∀ t<n, ∃ a, Heavy E f (state E f t).1 a) :
    ((state E f n).1.card:ℝ)<(Fintype.card ι:ℝ)*(1-f)^n := by
  cases n with
  | zero => omega
  | succ n =>
    have hStep := step_card_lt E f (state E f n) (hHeavy n (by omega))
    have hPrev := remainder_card_le_power E f hf n (fun t ht ↦ hHeavy t (by omega))
    calc
      _ < (1-f)*((state E f n).1.card:ℝ) := hStep
      _ ≤ (1-f)*((Fintype.card ι:ℝ)*(1-f)^n) := mul_le_mul_of_nonneg_left hPrev (by linarith)
      _ = _ := by rw [pow_succ]; ring

theorem exists_thin_remainder (E : ι → ι → Prop) (hE : Observable E) (f : ℝ) (hf : f≤1)
    (r : ℕ) (hr : 1≤r) (hγ : r<dominationNumber E hE)
    (hSmall : (Fintype.card ι:ℝ)*(1-f)^r≤1) :
    ∃ W : Finset ι, W.Nonempty ∧ (∀ a, ((observedMembers E W a).card:ℝ)≤f*(W.card:ℝ)) ∧
      1≤f*(W.card:ℝ) := by
  have hStop : ∃ n<r, ¬ ∃ a, Heavy E f (state E f n).1 a := by
    by_contra hNo
    have hAll : ∀ n<r, ∃ a, Heavy E f (state E f n).1 a := by
      intro n hn
      by_contra h
      exact hNo ⟨n,hn,h⟩
    have hStrict := (remainder_card_lt_power E f hf r hr hAll).trans_le hSmall
    have hNonempty := remainder_nonempty E hE f r hγ
    have hOne : (1:ℝ)≤((state E f r).1.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hNonempty
    linarith
  obtain ⟨n,hn,hStop⟩ := hStop
  have hW := remainder_nonempty E hE f n (by omega)
  have hEach : ∀ a, ((observedMembers E (state E f n).1 a).card:ℝ)≤f*((state E f n).1.card:ℝ) := by
    intro a
    exact le_of_not_gt (fun ha ↦ hStop ⟨a,ha⟩)
  refine ⟨(state E f n).1,hW,hEach,?_⟩
  obtain ⟨v,hv⟩ := hW
  obtain ⟨a,hav⟩ := hE v
  have hMem : v∈observedMembers E (state E f n).1 a := Finset.mem_filter.mpr ⟨hv,hav⟩
  have hOne : (1:ℝ)≤((observedMembers E (state E f n).1 a).card:ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨v,hMem⟩
  exact hOne.trans (hEach a)

end
end Tournament.ObserverThinning
