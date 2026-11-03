module

public import Tournament.Lower.Environments
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Tournament.Lower

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} {S : Finset ι}

def totalClippingError (θ : ℝ) (j : Coordinate S) (sign : ℝ) (x : Coordinate S → ℝ) : ℝ :=
  ∑ u : S, |clip (rawLoss θ j sign x u)-rawLoss θ j sign x u|

def memberNoise (a : ι) (sign : ℝ) (x : Coordinate S → ℝ) (v : S) : ℝ :=
  ∑ u : S, if a=u.val then sign*(x (some u)-x (some v)) else 0

theorem totalClippingError_nonneg (θ : ℝ) (j : Coordinate S) (sign : ℝ) (x : Coordinate S → ℝ) :
    0≤totalClippingError θ j sign x := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem memberNoise_atMember (u : S) (sign : ℝ) (x : Coordinate S → ℝ) (v : S) :
    memberNoise u.val sign x v=sign*(x (some u)-x (some v)) := by
  unfold memberNoise
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hbu
    have hb : u.val≠b.val := by intro h; exact hbu (Subtype.ext h.symm)
    simp only [ite_eq_right hb]
  · intro hu
    exact False.elim (hu (Finset.mem_univ u))

theorem memberNoise_outside {a : ι} (ha : a∉S) (sign : ℝ) (x : Coordinate S → ℝ) (v : S) :
    memberNoise a sign x v=0 := by
  apply Finset.sum_eq_zero
  intro u _
  have hne : a≠u.val := by intro h; exact ha (h.symm ▸ u.property)
  exact ite_eq_right hne

theorem clipping_pair_le_total (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (u v : S) :
    |clip (rawLoss θ j sign x u)-rawLoss θ j sign x u|+
      |clip (rawLoss θ j sign x v)-rawLoss θ j sign x v|≤2*totalClippingError θ j sign x := by
  have hu : |clip (rawLoss θ j sign x u)-rawLoss θ j sign x u|≤totalClippingError θ j sign x :=
    Finset.single_le_sum (f := fun a : S ↦ |clip (rawLoss θ j sign x a)-rawLoss θ j sign x a|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ u)
  have hv : |clip (rawLoss θ j sign x v)-rawLoss θ j sign x v|≤totalClippingError θ j sign x :=
    Finset.single_le_sum (f := fun a : S ↦ |clip (rawLoss θ j sign x a)-rawLoss θ j sign x a|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ v)
  linarith

theorem clipped_gap_ge_raw (r s : ℝ) :
    r-s-|clip r-r|-|clip s-s|≤clip r-clip s := by
  have hr := neg_abs_le (clip r-r)
  have hs := le_abs_self (clip s-s)
  linarith

theorem raw_gap_chosen (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (u v : S) (hj : j=none ∨ j=some v) :
    rawLoss θ j sign x u-rawLoss θ j sign x v=
      sign*(x (some u)-x (some v))+θ*(if j=some v then 1 else 0)*(if u=v then 0 else 1) := by
  rcases hj with rfl | rfl
  · simp [rawLoss]
    ring
  · by_cases huv : u=v
    · subst u
      simp [rawLoss]
    · have hvu : some v≠some u := by intro h; exact huv (Option.some.inj h).symm
      simp [rawLoss,hvu,huv]
      ring

theorem round_regret_comparison (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (a : ι) (v : S) (hj : j=none ∨ j=some v) :
    memberNoise a sign x v+θ*(if j=some v then 1 else 0)*
      (1-(if a=v.val then 1 else 0)-(if a∈S then 0 else 1))+
      (1/4)*(if a∈S then 0 else 1)-2*totalClippingError θ j sign x
      ≤environmentLoss θ j sign x a-environmentLoss θ j sign x v := by
  by_cases ha : a∈S
  · let u : S := ⟨a,ha⟩
    have hnoise := memberNoise_atMember u sign x v
    have hraw := raw_gap_chosen θ j sign x u v hj
    have hclip := clipped_gap_ge_raw (rawLoss θ j sign x u) (rawLoss θ j sign x v)
    have herr := clipping_pair_le_total θ j sign x u v
    have haMem : u.val=a := rfl
    rw [haMem] at hnoise
    have hA : environmentLoss θ j sign x a=clip (rawLoss θ j sign x u) := by
      simp only [environmentLoss,dite_eq_left ha]
      rfl
    have hV : environmentLoss θ j sign x v=clip (rawLoss θ j sign x v) := by
      simp only [environmentLoss,dite_eq_left v.property]
    rw [hnoise,hA,hV]
    simp only [ite_eq_left ha,mul_zero,add_zero,sub_zero]
    by_cases hav : a=v.val
    · have huv : u=v := Subtype.ext hav
      rw [huv]
      simp only [ite_eq_left hav,sub_self,mul_zero,add_zero]
      have he := totalClippingError_nonneg θ j sign x
      linarith
    · have huv : u≠v := by intro h; exact hav (congrArg Subtype.val h)
      simp only [ite_eq_right huv,mul_one] at hraw
      simp only [ite_eq_right hav,sub_zero,mul_one]
      linarith
  · have hav : a≠v.val := by intro h; exact ha (h.symm ▸ v.property)
    have hnoise := memberNoise_outside ha sign x v
    have hgap := outside_gap θ j sign x ha v
    have herr := totalClippingError_nonneg θ j sign x
    simp only [hnoise,ite_eq_right hav,ite_eq_right ha,sub_zero,sub_self,mul_zero,zero_add,mul_one]
    linarith

end
end Tournament.Lower
