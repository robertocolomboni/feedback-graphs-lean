module

public import Tournament.Lower.SignFlips
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Lower.FairSigns

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

variable {T : ℕ}

def partialSum (s : Finset (Fin T)) (ω : Space T) : ℝ := ∑ t∈s, sign t ω

theorem partialSum_flip (s : Finset (Fin T)) (t : Fin T) (ht : t∉s) (ω : Space T) :
    partialSum s (flip t ω)=partialSum s ω := by
  apply Finset.sum_congr rfl
  intro u hu
  exact sign_flip_other t u (fun h ↦ ht (h ▸ hu)) ω

theorem fresh_mixed_mean_zero (s : Finset (Fin T)) (t : Fin T) (ht : t∉s) (n : ℕ) :
    (∫ ω, sign t ω*(partialSum s ω)^n ∂law T)=0 := by
  have hSame := (flip_preserving T t).hasLaw.integral_comp
    (Measurable.of_discrete (f := fun ω ↦ sign t ω*(partialSum s ω)^n)).aestronglyMeasurable
  simp only [Function.comp_apply] at hSame
  have hFlip (ω : Space T) : sign t (flip t ω)*(partialSum s (flip t ω))^n=
      -(sign t ω*(partialSum s ω)^n) := by
    rw [sign_flip,partialSum_flip s t ht]
    ring
  have hNeg : (∫ ω, sign t (flip t ω)*(partialSum s (flip t ω))^n ∂law T)=
      -(∫ ω, sign t ω*(partialSum s ω)^n ∂law T) := by
    calc
      _ = ∫ ω, -(sign t ω*(partialSum s ω)^n) ∂law T :=
        integral_congr_ae (Filter.Eventually.of_forall hFlip)
      _ = _ := integral_neg _
  linarith

theorem partialSum_second (s : Finset (Fin T)) :
    (∫ ω, (partialSum s ω)^2 ∂law T)=(s.card:ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [partialSum]
  | @insert t s ht ih =>
    have hExpand (ω : Space T) : (partialSum (insert t s) ω)^2=
        (partialSum s ω)^2+2*(sign t ω*partialSum s ω)+1 := by
      simp only [partialSum,Finset.sum_insert ht]
      nlinarith [sign_square t ω]
    have hMixed : (∫ ω, sign t ω*partialSum s ω ∂law T)=0 := by
      simpa only [pow_one] using fresh_mixed_mean_zero s t ht 1
    calc
      _ = ∫ ω, (partialSum s ω)^2+2*(sign t ω*partialSum s ω)+1 ∂law T :=
        integral_congr_ae (Filter.Eventually.of_forall hExpand)
      _ = (s.card:ℝ)+1 := by
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_const_mul,ih,hMixed]
        simp
      _ = _ := by rw [Finset.card_insert_of_notMem ht,Nat.cast_add,Nat.cast_one]

theorem fourth_expansion (a b : ℝ) (ha : a^2=1) :
    (a+b)^4=b^4+4*(a*b^3)+6*b^2+4*(a*b)+1 := by
  have ha3 : a^3=a := by rw [pow_succ,ha,one_mul]
  have ha4 : a^4=1 := by rw [show a^4=(a^2)^2 by ring,ha]; norm_num
  calc
    _ = b^4+4*(a*b^3)+6*a^2*b^2+4*(a^3*b)+a^4 := by ring
    _ = _ := by rw [ha,ha3,ha4]; ring

theorem partialSum_fourth (s : Finset (Fin T)) :
    (∫ ω, (partialSum s ω)^4 ∂law T)=3*(s.card:ℝ)^2-2*(s.card:ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [partialSum]
  | @insert t s ht ih =>
    have hExpand (ω : Space T) : (partialSum (insert t s) ω)^4=
        (partialSum s ω)^4+4*(sign t ω*(partialSum s ω)^3)+
          6*(partialSum s ω)^2+4*(sign t ω*partialSum s ω)+1 := by
      rw [partialSum,Finset.sum_insert ht]
      exact fourth_expansion _ _ (sign_square t ω)
    have hMixed1 : (∫ ω, sign t ω*partialSum s ω ∂law T)=0 := by
      simpa only [pow_one] using fresh_mixed_mean_zero s t ht 1
    calc
      _ = ∫ ω, (partialSum s ω)^4+4*(sign t ω*(partialSum s ω)^3)+
          6*(partialSum s ω)^2+4*(sign t ω*partialSum s ω)+1 ∂law T :=
        integral_congr_ae (Filter.Eventually.of_forall hExpand)
      _ = 3*(s.card:ℝ)^2-2*(s.card:ℝ)+6*(s.card:ℝ)+1 := by
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite]
        simp only [integral_const_mul,ih,partialSum_second,
          fresh_mixed_mean_zero s t ht 3,hMixed1,mul_zero,add_zero,integral_const,
          probReal_univ,one_smul]
      _ = _ := by rw [Finset.card_insert_of_notMem ht,Nat.cast_add,Nat.cast_one]; ring

theorem sum_second : (∫ ω, (∑ t : Fin T, sign t ω)^2 ∂law T)=(T:ℝ) := by
  simpa only [partialSum,Finset.card_univ,Fintype.card_fin] using partialSum_second (Finset.univ : Finset (Fin T))

theorem sum_fourth : (∫ ω, (∑ t : Fin T, sign t ω)^4 ∂law T)=3*(T:ℝ)^2-2*(T:ℝ) := by
  simpa only [partialSum,Finset.card_univ,Fintype.card_fin] using partialSum_fourth (Finset.univ : Finset (Fin T))

end
end Tournament.Lower.FairSigns
