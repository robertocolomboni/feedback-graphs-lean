module

public import Tournament.Upper.GeometricMissedExpectation
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open MeasureTheory
open scoped Classical BigOperators unitInterval
noncomputable section

def shiftedLoss (d : ℕ → ℝ) (t : ℕ) (i : Bool) : ℝ := if i then d t else 0

theorem shifted_accumulated (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    Model.accumulatedLoss T (shiftedLoss d) (arm d coins)=playedGain d coins T := by
  apply Finset.sum_congr rfl
  intro t _
  cases h : arm d coins t with
  | false =>
    have hp : ¬Playing d coins t := by change arm d coins t≠true; simp [h]
    simp [shiftedLoss,hp]
  | true =>
    have hp : Playing d coins t := h
    simp [shiftedLoss,hp]

theorem shifted_fixed_true (d : ℕ → ℝ) (T : ℕ) : Model.fixedLoss T (shiftedLoss d) true=cumulative d T := rfl

theorem shifted_fixed_false (d : ℕ → ℝ) (T : ℕ) : Model.fixedLoss T (shiftedLoss d) false=0 := by
  simp [Model.fixedLoss,shiftedLoss]

theorem shifted_best (d : ℕ → ℝ) (T : ℕ) : Model.bestFixedLoss T (shiftedLoss d)=min (cumulative d T) 0 := by
  apply le_antisymm
  · apply le_min
    · simpa only [shifted_fixed_true] using Model.bestFixedLoss_le T (shiftedLoss d) true
    · simpa only [shifted_fixed_false] using Model.bestFixedLoss_le T (shiftedLoss d) false
  · apply Finset.le_inf'
    intro i _
    cases i with
    | false => rw [shifted_fixed_false]; exact min_le_right _ _
    | true => rw [shifted_fixed_true]; exact min_le_left _ _

theorem shifted_regret (d : ℕ → ℝ) (coins : ℕ → Bool) (T : ℕ) :
    Model.pathRegret T (shiftedLoss d) (arm d coins)=
      playedGain d coins T+(Model.switchCount T (arm d coins):ℝ)-min (cumulative d T) 0 := by
  rw [Model.pathRegret,shifted_accumulated,shifted_best]

theorem expected_switches_le (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) :
    (∫ ω, (Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p)≤2*(p:ℝ)*(T:ℝ) := by
  have hPoint (ω : CoinSpace T) :
      (Model.switchCount T (arm d (coinPath ω)):ℝ)≤2*(probeCount d (coinPath ω) T:ℝ) := by
    exact_mod_cast switches_le_twice_probes d (coinPath ω) T
  have h := integral_mono (μ := coinLaw T p) Integrable.of_finite Integrable.of_finite hPoint
  rw [integral_const_mul] at h
  have hN := expected_probeCount_le d T p
  nlinarith

theorem expected_blind_comparison (d : ℕ → ℝ) (T : ℕ) (p : unitInterval)
    (hd : ∀ t<T, d t≤1) :
    (∫ ω, playedGain d (coinPath ω) T+(Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p)≤3*(p:ℝ)*(T:ℝ) := by
  have h := integral_mono (μ := coinLaw T p) Integrable.of_finite Integrable.of_finite
    (fun ω ↦ blind_comparison_le d (coinPath ω) T hd)
  rw [integral_const_mul] at h
  have hN := expected_probeCount_le d T p
  nlinarith

theorem expected_revealing_comparison (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) (hp : 0<(p:ℝ))
    (hd : ∀ t<T, -1≤d t ∧ d t≤1) :
    (∫ ω, playedGain d (coinPath ω) T-cumulative d T+
      (Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p)≤1/(p:ℝ)+3*(p:ℝ)*(T:ℝ) := by
  have hEqual : (∫ ω, playedGain d (coinPath ω) T-cumulative d T+
        (Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p)=
      ∫ ω, -restingGain d (coinPath ω) T+(Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hPartition := cumulative_eq_played_add_resting d (coinPath ω) T
    linarith
  rw [hEqual,integral_add Integrable.of_finite Integrable.of_finite]
  have hMiss := expected_missed_advantage d T p hp hd
  have hN := expected_probeCount_le d T p
  have hSwitch := expected_switches_le d T p
  nlinarith

theorem geometric_probing (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) (hp : 0<(p:ℝ))
    (hd : ∀ t<T, -1≤d t ∧ d t≤1) :
    (∫ ω, Model.pathRegret T (shiftedLoss d) (arm d (coinPath ω)) ∂coinLaw T p)≤
      1/(p:ℝ)+3*(p:ℝ)*(T:ℝ) ∧
    (∫ ω, (Model.switchCount T (arm d (coinPath ω)):ℝ) ∂coinLaw T p)≤2*(p:ℝ)*(T:ℝ) := by
  refine ⟨?_,expected_switches_le d T p⟩
  by_cases hD : 0≤cumulative d T
  · have hFn : (fun ω : CoinSpace T ↦ Model.pathRegret T (shiftedLoss d) (arm d (coinPath ω)))=
        fun ω ↦ playedGain d (coinPath ω) T+(Model.switchCount T (arm d (coinPath ω)):ℝ) := by
      funext ω
      rw [shifted_regret,min_eq_right hD,sub_zero]
    rw [hFn]
    have h := expected_blind_comparison d T p (fun t ht ↦ (hd t ht).2)
    have hInv : 0≤1/(p:ℝ) := by positivity
    linarith
  · have hFn : (fun ω : CoinSpace T ↦ Model.pathRegret T (shiftedLoss d) (arm d (coinPath ω)))=
        fun ω ↦ playedGain d (coinPath ω) T-cumulative d T+(Model.switchCount T (arm d (coinPath ω)):ℝ) := by
      funext ω
      rw [shifted_regret,min_eq_left (le_of_not_ge hD)]
      ring
    rw [hFn]
    exact expected_revealing_comparison d T p hp hd

def tunedRate (T : ℕ) : ℝ := 1/Real.sqrt (3*(T:ℝ))

theorem tunedRate_bounds (T : ℕ) (hT : 1≤T) : 0<tunedRate T ∧ tunedRate T≤1 := by
  have hT0 : (1:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  have hS : 0<Real.sqrt (3*(T:ℝ)) := by positivity
  have hSq := Real.sq_sqrt (show (0:ℝ)≤3*(T:ℝ) by positivity)
  have hS1 : 1≤Real.sqrt (3*(T:ℝ)) := by nlinarith [Real.sqrt_nonneg (3*(T:ℝ))]
  exact ⟨one_div_pos.mpr hS,(div_le_one hS).mpr hS1⟩

theorem tuned_budget (T : ℕ) (hT : 1≤T) : 1/tunedRate T+3*tunedRate T*(T:ℝ)=2*Real.sqrt (3*(T:ℝ)) := by
  have hT0 : (1:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  have hS : 0<Real.sqrt (3*(T:ℝ)) := by positivity
  have hSq := Real.sq_sqrt (show (0:ℝ)≤3*(T:ℝ) by positivity)
  unfold tunedRate
  field_simp
  nlinarith

theorem tuned_geometric_probing (T : ℕ) (hT : 1≤T) :
    ∃ p : unitInterval, (p:ℝ)=tunedRate T ∧ ∀ d : ℕ → ℝ, (∀ t<T, -1≤d t ∧ d t≤1) →
      (∫ ω, Model.pathRegret T (shiftedLoss d) (arm d (coinPath ω)) ∂coinLaw T p)≤2*Real.sqrt (3*(T:ℝ)) := by
  have hRate := tunedRate_bounds T hT
  let p : unitInterval := ⟨tunedRate T,hRate.1.le,hRate.2⟩
  refine ⟨p,rfl,?_⟩
  intro d hd
  have h := (geometric_probing d T p hRate.1 hd).1
  simpa only [show (p:ℝ)=tunedRate T from rfl,tuned_budget T hT] using h

end
end Tournament.Upper.GeometricProbing
