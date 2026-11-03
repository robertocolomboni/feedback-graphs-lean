module

public import Tournament.Characterization.Main

@[expose] public section

namespace Tournament.Characterization

open Model.MeasurableGame Lower.Domination
open scoped Classical
noncomputable section

def middleScale (γ T : ℕ) : ℝ :=
  min (T:ℝ) ((γ:ℝ)^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3))

theorem min_scale_comparison (x T c d : ℝ) (hx : 0 ≤ x) (hT : 0 ≤ T)
    (hc : 1 ≤ c) (hcd : c ≤ d) :
    min T x ≤ min (c*x) T ∧ min (c*x) T ≤ d*min T x := by
  constructor
  · exact le_min ((min_le_right _ _).trans (by nlinarith)) (min_le_left _ _)
  · by_cases hTx : T ≤ x
    · rw [min_eq_left hTx]
      exact (min_le_right _ _).trans (by nlinarith)
    · rw [min_eq_right (le_of_not_ge hTx)]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hcd hx)

theorem log_cube_root_factors (K : ℕ) (hK : 2 ≤ K) :
    1 ≤ 5*(Real.log (K:ℝ))^((1:ℝ)/3) ∧
      5*(Real.log (K:ℝ))^((1:ℝ)/3) ≤ 5*logCard K := by
  have hL := Upper.Tuning.log_card_lower hK
  have hL0 : 0 ≤ Real.log (K:ℝ) := by linarith
  have hr0 := Real.rpow_nonneg hL0 ((1:ℝ)/3)
  have hx := logCard_ge_one K hK
  have hx0 : 0 ≤ logCard K := by linarith
  have hr := root_cube (Real.log (K:ℝ)) hL0
  constructor
  · apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 1)
      (mul_nonneg (by norm_num) hr0) (by decide : (3:ℕ) ≠ 0)).mp
    rw [mul_pow, hr]
    norm_num
    linarith
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 5)
    apply (pow_le_pow_iff_left₀ hr0 hx0 (by decide : (3:ℕ) ≠ 0)).mp
    rw [hr]
    have hsq : 1 ≤ (logCard K)^2 := by nlinarith
    have hcube : logCard K ≤ (logCard K)^3 := by
      nlinarith [mul_nonneg hx0 (show 0 ≤ (logCard K)^2-1 by linarith)]
    dsimp [logCard] at hx hcube ⊢
    linarith

theorem middleScale_comparison (K γ T : ℕ) (hK : 2 ≤ K) :
    middleScale γ T ≤
        min (5*((γ:ℝ)*Real.log (K:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ) ∧
      min (5*((γ:ℝ)*Real.log (K:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ) ≤
        5*logCard K*middleScale γ T := by
  obtain ⟨hc,hcd⟩ := log_cube_root_factors K hK
  have h := min_scale_comparison
    ((γ:ℝ)^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ)
    (5*(Real.log (K:ℝ))^((1:ℝ)/3)) (5*logCard K)
    (by positivity) (by positivity) hc hcd
  have hL0 : 0 ≤ Real.log (K:ℝ) := by linarith [Upper.Tuning.log_card_lower hK]
  simpa only [middleScale, Real.mul_rpow (Nat.cast_nonneg γ) hL0,
    mul_assoc, mul_comm, mul_left_comm] using h

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem intro_strongly_revealing (E : ι → ι → Prop) (hE : StronglyRevealing E)
    (hK : 2 ≤ Fintype.card ι) (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt (T:ℝ)/4 ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤
        ((2:ℝ)^40*Real.sqrt (Real.log (Fintype.card ι:ℝ))*
          (Real.log (Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ)))^2)*Real.sqrt (T:ℝ) := by
  obtain ⟨hl,hu⟩ := strongly_revealing E hE hK T hT
  refine ⟨hl,?_⟩
  simpa only [Real.sqrt_mul (Nat.cast_nonneg T), mul_assoc, mul_comm, mul_left_comm] using hu

theorem intro_observable_nonrevealing (E : ι → ι → Prop)
    (hObs : Observable E) (hNot : ¬StronglyRevealing E)
    (hK : 2 ≤ Fintype.card ι) (T : ℕ) (hT : 2 ≤ T) :
    middleScale (dominationNumber E hObs) T /
        (5120*(Real.log (2*(T:ℝ))/Real.log 2)*
          Real.log (Real.exp 1*(Fintype.card ι:ℝ))) ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤
        (5*Real.log (Real.exp 1*(Fintype.card ι:ℝ)))*middleScale (dominationNumber E hObs) T := by
  let K := Fintype.card ι
  let γ := dominationNumber E hObs
  have hK' : 2 ≤ K := hK
  have hLow : bound K γ T ≤ minimax.{u,0} T E := by
    simpa only [bound, logCard_eq K hK', Lower.Dyadic.upsilon] using
      (observable_nonrevealing E hObs hNot hK T hT).1
  have hHigh := (observable_nonrevealing E hObs hNot hK T hT).2
  obtain ⟨hsLow,hsHigh⟩ := middleScale_comparison K γ T hK'
  have hc : 0 < 5120*Lower.Dyadic.upsilon T*logCard K := by
    have hu := Lower.Parameters.upsilon_ge_one T (by omega)
    have hk := logCard_ge_one K hK'
    positivity
  constructor
  · have h := hsLow.trans ((upper_lower_ratio K γ T hK' hT).trans
        (mul_le_mul_of_nonneg_left hLow hc.le))
    have hh : middleScale γ T / (5120*Lower.Dyadic.upsilon T*logCard K) ≤
        minimax.{u,0} T E := (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h)
    simpa only [Lower.Dyadic.upsilon, logCard_eq K hK'] using hh
  · have h := hHigh.trans hsHigh
    simpa only [logCard_eq K hK'] using h

theorem intro_nonobservable (E : ι → ι → Prop) (hNot : ¬Observable E)
    (hK : 2 ≤ Fintype.card ι) (T : ℕ) :
    (T:ℝ)/4 ≤ minimax.{u,0} T E ∧ minimax.{u,0} T E ≤ (T:ℝ) :=
  Lower.Unobservable.minimax_bounds T E hNot hK

end
end Tournament.Characterization
