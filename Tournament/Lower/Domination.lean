module

public import Tournament.Lower.GraphWitnesses
public import Tournament.Lower.DominationNumerics

@[expose] public section

namespace Tournament.Lower.Domination

open MeasureTheory Model.MeasurableGame
open scoped Classical
noncomputable section

def bound (K γ T : ℕ) : ℝ :=
  (T:ℝ)^((2:ℝ)/3)*(max 1 (min (γ:ℝ) (T:ℝ)/(logCard K)^2))^((1:ℝ)/3)/
    (1024*Dyadic.upsilon T)

theorem bound_factor (K γ T : ℕ) :
    bound K γ T=((T:ℝ)^((2:ℝ)/3)/(256*Dyadic.upsilon T))*
      (max 1 (min (γ:ℝ) (T:ℝ)/(logCard K)^2))^((1:ℝ)/3)/4 := by
  unfold bound
  ring

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable [Fintype ι] [Nonempty ι] [MeasurableSpace Seed]

theorem lower_bound (ν : Measure Seed) [IsProbabilityMeasure ν]
    (T : ℕ) (hT : 2≤T) (π : Learner ι Seed) (E : ι → ι → Prop)
    (hObs : Observable E) (hNot : ¬StronglyRevealing E) (hK : 2≤Fintype.card ι) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      bound (Fintype.card ι) (dominationNumber E hObs) T≤deterministicExpectedRegret T ν π E loss := by
  let K := Fintype.card ι
  let γ := dominationNumber E hObs
  let x := logCard K
  let A := min (γ:ℝ) (T:ℝ)/x^2
  let base := (T:ℝ)^((2:ℝ)/3)/(256*Dyadic.upsilon T)
  have hx1 : 1≤x := logCard_ge_one K hK
  have hx : 0<x := by linarith
  have hBase : 0≤base := by
    have hU := Parameters.upsilon_ge_one T (by omega)
    dsimp [base]
    positivity
  obtain ⟨pairLoss,hPairBound,hPair⟩ := pair_lower_bound ν T hT π E hNot
  have hBoundFactor : bound K γ T=base*(max 1 A)^((1:ℝ)/3)/4 := bound_factor K γ T
  by_cases hSmall : (γ:ℝ)<32*Real.log (K:ℝ)
  · have hRatio : A≤8 := small_ratio_le_eight x γ T hx (by dsimp [x,logCard]; linarith)
    have hRoot := small_max_root_le_two A hRatio
    refine ⟨pairLoss,hPairBound,?_⟩
    apply le_trans _ hPair
    rw [hBoundFactor]
    dsimp only [base] at hBase ⊢
    nlinarith [mul_le_mul_of_nonneg_left hRoot hBase]
  · have hLarge : 32*Real.log (K:ℝ)≤(γ:ℝ) := le_of_not_gt hSmall
    obtain ⟨S,hSize,hNo,hCount⟩ := few_observers E hObs hK hLarge
    have hLog : 0<Real.log (K:ℝ) := by linarith [Upper.Tuning.log_card_lower hK]
    have hTwo : (2:ℝ)≤(γ:ℝ)/(16*Real.log (K:ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0<16*Real.log (K:ℝ))).mpr
      linarith
    have hS : 2≤S.card := by exact_mod_cast hTwo.trans hSize
    have hCount' (a : ι) : ((observed E S a).card:ℝ)≤x := hCount a
    obtain ⟨loss,hBound,hReg⟩ := Tournament.Lower.lower_bound ν hT π E
      (sparse_of_no_distinct_edges E S hNo) hS x hx1 hCount'
    have hWeakSize : (γ:ℝ)/(16*x)≤(S.card:ℝ) := by
      calc
        _ ≤ (γ:ℝ)/(16*Real.log (K:ℝ)) := div_le_div_of_nonneg_left (Nat.cast_nonneg γ)
          (by positivity) (by dsimp [x,logCard]; linarith)
        _ ≤ _ := hSize
    have hMin := truncated_size (γ:ℝ) (S.card:ℝ) (T:ℝ) (16*x)
      (by linarith) (Nat.cast_nonneg T) hWeakSize
    let B := min (S.card:ℝ) (T:ℝ)/x
    have hA0 : 0≤A := by dsimp [A]; positivity
    have hB0 : 0≤B := by dsimp [B]; positivity
    have hAB : A≤16*B := truncated_ratio γ S.card T x hx hMin
    have hRoot := quarter_root_le A B hA0 hB0 hAB
    by_cases hA : A≤1
    · refine ⟨pairLoss,hPairBound,?_⟩
      apply le_trans _ hPair
      rw [hBoundFactor,max_eq_left hA,Real.one_rpow,mul_one]
      change base/4≤base
      linarith
    · refine ⟨loss,hBound,?_⟩
      apply le_trans _ hReg
      rw [hBoundFactor,max_eq_right (le_of_not_ge hA)]
      have hMul := mul_le_mul_of_nonneg_left hRoot hBase
      dsimp [base,B] at hMul ⊢
      convert hMul using 1 <;> ring

end
end Tournament.Lower.Domination
