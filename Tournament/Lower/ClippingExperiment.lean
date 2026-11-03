module

public import Tournament.Lower.WalkSignExperiment
public import Tournament.Lower.ClippingConstants

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

def incrementVariance (T : ℕ) : ℝ≥0 := ⟨(Parameters.sigma T)^2,sq_nonneg _⟩

def environmentLaw {ι : Type*} (S : Finset ι) (T : ℕ) :
    Measure (WalkSign.Space T (Coordinate S)) := WalkSign.law T (incrementVariance T)

instance environmentLaw_probability {ι : Type*} (S : Finset ι) (T : ℕ) :
    IsProbabilityMeasure (environmentLaw S T) := by
  unfold environmentLaw
  infer_instance

def sampledRawLoss {ι : Type*} {S : Finset ι} {T : ℕ} (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (v : S) (ω : WalkSign.Space T (Coordinate S)) : ℝ :=
  rawLoss θ j (WalkSign.sign t ω) (fun c ↦ WalkSign.walk c (t.val+1) ω) v

def clippingError {ι : Type*} {S : Finset ι} {T : ℕ} (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (v : S) (ω : WalkSign.Space T (Coordinate S)) : ℝ :=
  |clip (sampledRawLoss θ j t v ω)-sampledRawLoss θ j t v ω|

theorem sampledRawLoss_as_mean {ι : Type*} {S : Finset ι} {T : ℕ}
    (θ : ℝ) (j : Coordinate S) (t : Fin T) (v : S) (ω : WalkSign.Space T (Coordinate S)) :
    sampledRawLoss θ j t v ω=(1/2-θ*(if j=some v then 1 else 0))+
      WalkSign.gaussianPart none (some v) t ω := by
  unfold sampledRawLoss rawLoss WalkSign.gaussianPart
  ring

theorem raw_mean_bounds {ι : Type*} {S : Finset ι} (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64)
    (j : Coordinate S) (v : S) :
    31/64≤1/2-θ*(if j=some v then 1 else 0) ∧
      1/2-θ*(if j=some v then 1 else 0)≤1/2 := by
  split_ifs <;> constructor <;> nlinarith

theorem gaussianPart_variance_parameter_le (T : ℕ) (hT : 2≤T) (t : Fin T) :
    ((2*((Dyadic.incrementSet T (t.val+1)).card • incrementVariance T):ℝ≥0):ℝ)
      ≤1/(128*Dyadic.upsilon T) := by
  have hU := Parameters.upsilon_ge_two T hT
  have hc : ((Dyadic.incrementSet T (t.val+1)).card:ℝ)≤Dyadic.upsilon T :=
    le_trans (by exact_mod_cast Dyadic.incrementSet_card_le T (t.val+1))
      (Dyadic.ancestor_depth T _ (by omega) (by omega))
  have hvar : (incrementVariance T:ℝ)=(Parameters.sigma T)^2 := rfl
  simp only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,nsmul_eq_mul,hvar]
  calc
    _ ≤ 2*Dyadic.upsilon T*(Parameters.sigma T)^2 := by
      have h := mul_le_mul_of_nonneg_right hc (sq_nonneg (Parameters.sigma T))
      nlinarith
    _ = _ := by
      unfold Parameters.sigma
      field_simp
      ring

theorem clippingError_integrable {ι : Type*} {S : Finset ι} {T : ℕ}
    (θ : ℝ) (j : Coordinate S) (t : Fin T) (v : S) :
    Integrable (clippingError θ j t v) (environmentLaw S T) := by
  have hg := WalkSign.gaussianPart_law T (incrementVariance T) none (some v) (by simp) t
  have h := clipping_error_hasLaw_integrable hg (1/2-θ*(if j=some v then 1 else 0))
  change Integrable (fun ω ↦ |clip (sampledRawLoss θ j t v ω)-sampledRawLoss θ j t v ω|)
    (WalkSign.law T (incrementVariance T))
  simp_rw [sampledRawLoss_as_mean]
  exact h

theorem clippingError_expectation_le {ι : Type*} {S : Finset ι} {T : ℕ}
    (hT : 2≤T) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (j : Coordinate S) (t : Fin T) (v : S) :
    (∫ ω, clippingError θ j t v ω ∂environmentLaw S T)≤(1/(2*(T:ℝ))^4)/20 := by
  have hg := WalkSign.gaussianPart_law T (incrementVariance T) none (some v) (by simp) t
  have h := clipping_error_hasLaw_le hg (1/2-θ*(if j=some v then 1 else 0))
    (raw_mean_bounds θ hθ j v)
  change (∫ ω, |clip (sampledRawLoss θ j t v ω)-sampledRawLoss θ j t v ω|
    ∂WalkSign.law T (incrementVariance T))≤_
  simp_rw [sampledRawLoss_as_mean]
  exact h.trans (clipping_gaussian_tail_le T hT _ (gaussianPart_variance_parameter_le T hT t))

theorem clipping_error_sum {ι : Type*} {S : Finset ι} {T : ℕ}
    (hT : 2≤T) (hST : S.card≤T) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (j : Coordinate S) :
    (∫ ω, ∑ t : Fin T, ∑ v : S, clippingError θ j t v ω ∂environmentLaw S T)≤1/1024 := by
  have hi (t : Fin T) : Integrable (fun ω ↦ ∑ v : S, clippingError θ j t v ω) (environmentLaw S T) :=
    integrable_finsetSum _ (fun v _ ↦ clippingError_integrable θ j t v)
  rw [integral_finsetSum _ (fun t _ ↦ hi t)]
  calc
    _ ≤ ∑ _t : Fin T, ∑ _v : S, (1/(2*(T:ℝ))^4)/20 := by
      apply Finset.sum_le_sum
      intro t _
      rw [integral_finsetSum _ (fun v _ ↦ clippingError_integrable θ j t v)]
      apply Finset.sum_le_sum
      intro v _
      exact clippingError_expectation_le hT θ hθ j t v
    _ = (T:ℝ)*(S.card:ℝ)*((1/(2*(T:ℝ))^4)/20) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]
      ring
    _ ≤ _ := clipping_sum_numerical_bound T S.card hT hST

theorem clipping_error_sum_parameters {ι : Type*} {S : Finset ι} {T : ℕ}
    (hT : 2≤T) (hST : S.card≤T) (m : ℕ) (hm : 1≤m) (j : Coordinate S) :
    (∫ ω, ∑ t : Fin T, ∑ v : S, clippingError (Parameters.theta T S.card m) j t v ω
      ∂environmentLaw S T)≤1/1024 :=
  clipping_error_sum hT hST _ ⟨Parameters.theta_nonneg T S.card m (by omega),
    Parameters.theta_le_one_sixty_four T S.card m hT hST hm⟩ j

end
end Tournament.Lower
