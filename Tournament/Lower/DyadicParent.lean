module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Tournament.Lower.Dyadic

open scoped BigOperators Classical

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def level (t : ℕ) : ℕ := padicValNat 2 t

def parent (t : ℕ) : ℕ := t-2^(level t)

def bandCount (T : ℕ) : ℕ := Nat.log 2 T+1

def upsilon (T : ℕ) : ℝ := Real.log (2*(T:ℝ))/Real.log 2

theorem level_power_dvd (t : ℕ) : 2^(level t)∣t := pow_padicValNat_dvd

theorem level_power_le (t : ℕ) (ht : 0<t) : 2^(level t)≤t := Nat.le_of_dvd ht (level_power_dvd t)

theorem parent_add_power (t : ℕ) (ht : 0<t) : parent t+2^(level t)=t :=
  Nat.sub_add_cancel (level_power_le t ht)

theorem parent_lt (t : ℕ) (ht : 0<t) : parent t<t :=
  Nat.sub_lt ht (pow_pos (by decide) _)

theorem odd_form (t : ℕ) (ht : 0<t) : ∃ y, t=2^(level t)*(2*y+1) := by
  obtain ⟨q,hq⟩ := level_power_dvd t
  have hnot : ¬2∣q := by
    intro hd
    obtain ⟨y,hy⟩ := hd
    apply pow_succ_padicValNat_not_dvd (p := 2) (Nat.ne_of_gt ht)
    refine ⟨y,?_⟩
    change t=2^(level t+1)*y
    calc
      t = 2^(level t)*q := hq
      _ = 2^(level t)*(2*y) := by rw [hy]
      _ = _ := by rw [pow_succ]; ring
  have hmod : q%2=1 := by
    have hlt := Nat.mod_lt q (by decide : 0<2)
    by_contra hn
    have hz : q%2=0 := by omega
    exact hnot (Nat.dvd_of_mod_eq_zero hz)
  refine ⟨q/2,?_⟩
  have heq : q=2*(q/2)+1 := by have h := Nat.mod_add_div q 2; omega
  calc
    t = 2^(level t)*q := hq
    _ = _ := congrArg (fun q : ℕ ↦ 2^(level t)*q) heq

theorem parent_of_odd_form (t y : ℕ) (h : t=2^(level t)*(2*y+1)) :
    parent t=2^(level t)*(2*y) := by
  unfold parent
  have heq : 2^(level t)*(2*y+1)=2^(level t)*(2*y)+2^(level t) := by ring
  conv_lhs => arg 1; rw [h]
  rw [heq,Nat.add_sub_cancel]

theorem parent_bits (t : ℕ) (ht : 0<t) : (parent t).bitIndices=t.bitIndices.tail := by
  obtain ⟨y,hy⟩ := odd_form t ht
  have hp := parent_of_odd_form t y hy
  conv_rhs => arg 1; rw [hy]
  rw [hp]
  simp only [Nat.bitIndices_two_pow_mul,Nat.bitIndices_two_mul,Nat.bitIndices_two_mul_add_one,
    List.map_cons,List.tail_cons]

theorem bits_nonempty (t : ℕ) (ht : 0<t) : t.bitIndices≠[] := by
  intro heq
  have hs := Nat.sum_map_two_pow_bitIndices t
  rw [heq] at hs
  simp only [List.map_nil,List.sum_nil] at hs
  omega

def ancestors (t : ℕ) : List ℕ :=
  if _ht : t=0 then [] else t::ancestors (parent t)
termination_by t
decreasing_by exact parent_lt t (Nat.pos_of_ne_zero _ht)

theorem ancestors_length (t : ℕ) : (ancestors t).length=t.bitIndices.length := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t=0
    · subst t
      simp [ancestors]
    · rw [ancestors,dite_eq_right ht,List.length_cons,ih (parent t) (parent_lt t (Nat.pos_of_ne_zero ht)),
        parent_bits t (Nat.pos_of_ne_zero ht)]
      have hbits := bits_nonempty t (Nat.pos_of_ne_zero ht)
      cases hb : t.bitIndices with
      | nil => exact False.elim (hbits hb)
      | cons a as => rfl

theorem mem_ancestors_bounds (t s : ℕ) (hs : s∈ancestors t) : 0<s ∧ s≤t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t=0
    · subst t
      simp [ancestors] at hs
    · rw [ancestors,dite_eq_right ht,List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨Nat.pos_of_ne_zero ht,le_rfl⟩
      · have hp := ih (parent t) (parent_lt t (Nat.pos_of_ne_zero ht)) hs
        exact ⟨hp.1,hp.2.trans (parent_lt t (Nat.pos_of_ne_zero ht)).le⟩

theorem ancestors_nodup (t : ℕ) : (ancestors t).Nodup := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t=0
    · subst t
      simp [ancestors]
    · rw [ancestors,dite_eq_right ht,List.nodup_cons]
      constructor
      · intro hmem
        have hp := mem_ancestors_bounds (parent t) t hmem
        have hlt := parent_lt t (Nat.pos_of_ne_zero ht)
        omega
      · exact ih (parent t) (parent_lt t (Nat.pos_of_ne_zero ht))

def walk (increment : ℕ → ℝ) (t : ℕ) : ℝ := ((ancestors t).map increment).sum

theorem walk_zero (increment : ℕ → ℝ) : walk increment 0=0 := by simp [walk,ancestors]

theorem walk_parent (increment : ℕ → ℝ) (t : ℕ) (ht : 0<t) :
    walk increment t=walk increment (parent t)+increment t := by
  unfold walk
  rw [ancestors,dite_eq_right (Nat.ne_of_gt ht),List.map_cons,List.sum_cons]
  ring

theorem level_le_log (T t : ℕ) (htT : t≤T) : level t≤Nat.log 2 T :=
  le_trans (padicValNat_le_nat_log t) (Nat.log_mono_right htT)

theorem bits_length_le (T t : ℕ) (htT : t≤T) : t.bitIndices.length≤bandCount T := by
  have hsubset : t.bitIndices.toFinset⊆Finset.range (bandCount T) := by
    intro k hk
    have hk' : k∈t.bitIndices := List.mem_toFinset.mp hk
    have hpow : 2^k≤T := (Nat.two_pow_le_of_mem_bitIndices hk').trans htT
    have hklog : k≤Nat.log 2 T := Nat.le_log_of_pow_le (by decide) hpow
    exact Finset.mem_range.mpr (by unfold bandCount; omega)
  have hc := Finset.card_le_card hsubset
  simpa only [List.toFinset_card_of_nodup Nat.bitIndices_nodup,Finset.card_range] using hc

theorem bandCount_le_upsilon (T : ℕ) (hT : 0<T) : (bandCount T:ℝ)≤upsilon T := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : (0:ℝ)<(T:ℝ) := by exact_mod_cast hT
  have hpow : (2:ℝ)^(Nat.log 2 T)≤(T:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hT)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 T)) hpow
  rw [Real.log_pow] at hl
  unfold upsilon bandCount
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt ht0)]
  apply (le_div_iff₀ hlog2).mpr
  push_cast
  nlinarith

theorem ancestor_depth (T t : ℕ) (hT : 0<T) (htT : t≤T) :
    ((ancestors t).length:ℝ)≤upsilon T := by
  rw [ancestors_length]
  exact le_trans (by exact_mod_cast bits_length_le T t htT) (bandCount_le_upsilon T hT)

end
end Tournament.Lower.Dyadic
