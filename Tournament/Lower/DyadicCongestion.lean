module

public import Tournament.Lower.DyadicParent
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Tournament.Lower.Dyadic

open scoped BigOperators Classical

noncomputable section

def children (T u : ℕ) : Finset ℕ := (Finset.Icc 1 T).filter (fun t ↦ parent t=u)

def crossings (T u : ℕ) : Finset ℕ := (Finset.Icc 1 T).filter (fun t ↦ parent t<u ∧ u≤t)

theorem children_level_injective (T u : ℕ) : Set.InjOn level (children T u) := by
  intro s hs t ht hlevel
  have hs' : 1≤s ∧ s≤T ∧ parent s=u := by simpa [children,and_assoc] using hs
  have ht' : 1≤t ∧ t≤T ∧ parent t=u := by simpa [children,and_assoc] using ht
  have hsp := parent_add_power s (by omega)
  have htp := parent_add_power t (by omega)
  rw [hs'.2.2,hlevel] at hsp
  rw [ht'.2.2] at htp
  omega

theorem children_card_le (T u : ℕ) : (children T u).card≤bandCount T := by
  rw [← Finset.card_range (bandCount T)]
  apply Finset.card_le_card_of_injOn level
  · intro t ht
    have htT : t≤T := ((Finset.mem_filter.mp ht).1 |> Finset.mem_Icc.mp).2
    exact Finset.mem_range.mpr (by have hl := level_le_log T t htT; unfold bandCount; omega)
  · exact children_level_injective T u

theorem equal_level_disjoint (s t u : ℕ) (hs : 0<s) (ht : 0<t) (hlevel : level s=level t)
    (hsu : parent s<u ∧ u≤s) (htu : parent t<u ∧ u≤t) : s=t := by
  obtain ⟨y,hy⟩ := odd_form s hs
  obtain ⟨z,hz⟩ := odd_form t ht
  have hpy := parent_of_odd_form s y hy
  have hpz := parent_of_odd_form t z hz
  rw [hlevel] at hy hpy
  rw [hpy] at hsu
  rw [hpz] at htu
  have hpow : 0<2^(level t) := pow_pos (by decide) _
  have hyz : y=z := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh : y+1≤z := by omega
      have hm := Nat.mul_le_mul_left (2^(level t)) hh
      nlinarith [hsu.1,hsu.2,htu.1,htu.2]
    · have hh : z+1≤y := by omega
      have hm := Nat.mul_le_mul_left (2^(level t)) hh
      nlinarith [hsu.1,hsu.2,htu.1,htu.2]
  calc
    s = 2^(level t)*(2*y+1) := hy
    _ = 2^(level t)*(2*z+1) := congrArg (fun q : ℕ ↦ 2^(level t)*(2*q+1)) hyz
    _ = t := hz.symm

theorem crossings_level_injective (T u : ℕ) : Set.InjOn level (crossings T u) := by
  intro s hs t ht hlevel
  have hs' := Finset.mem_filter.mp hs
  have ht' := Finset.mem_filter.mp ht
  exact equal_level_disjoint s t u (by have := (Finset.mem_Icc.mp hs'.1).1; omega)
    (by have := (Finset.mem_Icc.mp ht'.1).1; omega) hlevel hs'.2 ht'.2

theorem crossings_card_le (T u : ℕ) : (crossings T u).card≤bandCount T := by
  rw [← Finset.card_range (bandCount T)]
  apply Finset.card_le_card_of_injOn level
  · intro t ht
    have htT : t≤T := ((Finset.mem_filter.mp ht).1 |> Finset.mem_Icc.mp).2
    exact Finset.mem_range.mpr (by have hl := level_le_log T t htT; unfold bandCount; omega)
  · exact crossings_level_injective T u

theorem children_card_le_upsilon (T u : ℕ) (hT : 0<T) : ((children T u).card:ℝ)≤upsilon T :=
  le_trans (by exact_mod_cast children_card_le T u) (bandCount_le_upsilon T hT)

theorem crossings_card_le_upsilon (T u : ℕ) (hT : 0<T) : ((crossings T u).card:ℝ)≤upsilon T :=
  le_trans (by exact_mod_cast crossings_card_le T u) (bandCount_le_upsilon T hT)

end
end Tournament.Lower.Dyadic
