module

public import Tournament.Lower.RegretExecution
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Seed]
variable [Fintype ι] [Nonempty ι] {S : Finset ι} {T : ℕ}

omit [DiscreteMeasurableSpace ι] in
theorem learner_path_regret_comparison (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (v : S) (hj : j=none ∨ j=some v)
    (p : Seed × WalkSign.Space T (Coordinate S)) :
    noiseTotal π E θ j v p+θ*(if j=some v then 1 else 0)*
      ((T:ℝ)-visits π E θ j v p-outsideVisits π E θ j p)+
      (1/4)*outsideVisits π E θ j p+switchTotal π E θ j p-2*errorTotal θ j p
      ≤learnerRegretPath π E θ j p := by
  have hr (t : Fin T) := round_regret_comparison θ j (WalkSign.sign t p.2)
    (fun c ↦ WalkSign.walk c (t.val+1) p.2) (learnerAction π E θ j t.val p) v hj
  have hround (t : Fin T) :
      roundNoise π E θ j v t p+θ*(if j=some v then 1 else 0)*
        (1-memberIndicator π E θ j v t p-outsideIndicator π E θ j t p)+
        (1/4)*outsideIndicator π E θ j t p-2*roundError θ j t p
        ≤sampledLoss θ j t.val p.2 (learnerAction π E θ j t.val p)-sampledLoss θ j t.val p.2 v := by
    simpa only [sampledLoss,dite_eq_left t.isLt,roundNoise,memberIndicator,outsideIndicator,
      roundError,clippingError,sampledRawLoss,totalClippingError] using hr t
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ ↦ hround t)
  have hleft :
      (∑ t : Fin T, (roundNoise π E θ j v t p+θ*(if j=some v then 1 else 0)*
        (1-memberIndicator π E θ j v t p-outsideIndicator π E θ j t p)+
        (1/4)*outsideIndicator π E θ j t p-2*roundError θ j t p))=
      noiseTotal π E θ j v p+θ*(if j=some v then 1 else 0)*
        ((T:ℝ)-visits π E θ j v p-outsideVisits π E θ j p)+
        (1/4)*outsideVisits π E θ j p-2*errorTotal θ j p := by
    simp only [noiseTotal,visits,outsideVisits,errorTotal,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [hleft] at hsum
  have hright :
      (∑ t : Fin T, (sampledLoss θ j t.val p.2 (learnerAction π E θ j t.val p)-sampledLoss θ j t.val p.2 v))=
      Model.accumulatedLoss T (fun t ↦ sampledLoss θ j t p.2) (fun t ↦ learnerAction π E θ j t p)-
        Model.fixedLoss T (fun t ↦ sampledLoss θ j t p.2) v := by
    rw [Finset.sum_sub_distrib,Fin.sum_univ_eq_sum_range
      (fun t ↦ sampledLoss θ j t p.2 (learnerAction π E θ j t p)),
      Fin.sum_univ_eq_sum_range (fun t ↦ sampledLoss θ j t p.2 v)]
    rfl
  rw [hright] at hsum
  have hbest := Model.bestFixedLoss_le T (fun t ↦ sampledLoss θ j t p.2) v.val
  unfold learnerRegretPath Model.pathRegret switchTotal
  linarith

theorem lower_regret_unsimplified (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 2≤T) (hST : S.card≤T) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (j : Coordinate S) (v : S) (hj : j=none ∨ j=some v) :
    θ*(if j=some v then 1 else 0)*
      ((T:ℝ)-(∫ p, visits π E θ j v p ∂privateLaw ν S T)-
        (∫ p, outsideVisits π E θ j p ∂privateLaw ν S T))+
      (1/4)*(∫ p, outsideVisits π E θ j p ∂privateLaw ν S T)+
      (∫ p, switchTotal π E θ j p ∂privateLaw ν S T)-1/512≤expectedRegret (T := T) ν π E θ j := by
  let Z := noiseTotal (T := T) π E θ j v
  let C := visits (T := T) π E θ j v
  let O := outsideVisits (T := T) π E θ j
  let N := switchTotal (T := T) π E θ j
  let F := errorTotal (T := T) (Seed := Seed) θ j
  let δ : ℝ := θ*(if j=some v then 1 else 0)
  have hZ : Integrable Z (privateLaw ν S T) := noiseTotal_integrable ν π E θ j v
  have hC : Integrable C (privateLaw ν S T) := visits_integrable ν π E θ j v
  have hO : Integrable O (privateLaw ν S T) := outsideVisits_integrable ν π E θ j
  have hN : Integrable N (privateLaw ν S T) := switchTotal_integrable ν π E θ j
  have hF : Integrable F (privateLaw ν S T) := errorTotal_integrable ν θ j
  have hgap : Integrable (fun p ↦ (T:ℝ)-C p-O p) (privateLaw ν S T) :=
    ((integrable_const (T:ℝ)).sub hC).sub hO
  have hδ := hgap.const_mul δ
  have hquarter := hO.const_mul (1/4:ℝ)
  have htwo := hF.const_mul (2:ℝ)
  have hsum := (((hZ.add hδ).add hquarter).add hN).sub htwo
  have hcompare := integral_mono hsum (learnerRegretPath_integrable ν π E θ j)
    (fun p ↦ learner_path_regret_comparison π E θ j v hj p)
  have hformula :
      (∫ p, Z p+δ*((T:ℝ)-C p-O p)+(1/4)*O p+N p-2*F p ∂privateLaw ν S T)=
      δ*((T:ℝ)-(∫ p, C p ∂privateLaw ν S T)-(∫ p, O p ∂privateLaw ν S T))+
      (1/4)*(∫ p, O p ∂privateLaw ν S T)+(∫ p, N p ∂privateLaw ν S T)-
      2*(∫ p, F p ∂privateLaw ν S T) := by
    rw [integral_sub (f := fun p ↦ Z p+δ*((T:ℝ)-C p-O p)+(1/4)*O p+N p)
        (g := fun p ↦ 2*F p) (((hZ.add hδ).add hquarter).add hN) htwo,
      integral_add (f := fun p ↦ Z p+δ*((T:ℝ)-C p-O p)+(1/4)*O p) (g := N)
        ((hZ.add hδ).add hquarter) hN,
      integral_add (f := fun p ↦ Z p+δ*((T:ℝ)-C p-O p)) (g := fun p ↦ (1/4)*O p)
        (hZ.add hδ) hquarter,integral_add hZ hδ,
      integral_const_mul,integral_const_mul,integral_const_mul,
      integral_sub (f := fun p ↦ (T:ℝ)-C p) (g := O) ((integrable_const (T:ℝ)).sub hC) hO,
      integral_sub (integrable_const (T:ℝ)) hC]
    have hz : ∫ p, Z p ∂privateLaw ν S T=0 := noiseTotal_mean_zero ν π E θ j v
    rw [hz,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul,zero_add]
  have herr : (∫ p, F p ∂privateLaw ν S T)≤1/1024 := errorTotal_expectation_le ν hT hST θ hθ j
  change (∫ p, Z p+δ*((T:ℝ)-C p-O p)+(1/4)*O p+N p-2*F p ∂privateLaw ν S T)≤
    expectedRegret (T := T) ν π E θ j at hcompare
  rw [hformula] at hcompare
  change δ*((T:ℝ)-(∫ p, C p ∂privateLaw ν S T)-(∫ p, O p ∂privateLaw ν S T))+
    (1/4)*(∫ p, O p ∂privateLaw ν S T)+(∫ p, N p ∂privateLaw ν S T)-1/512≤_
  linarith

theorem lower_regret_reference (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 2≤T) (hST : S.card≤T) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (v : S) :
    (∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)+
      (1/4)*(∫ p, outsideVisits (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)-1/512
      ≤expectedRegret (T := T) ν π E θ (none : Coordinate S) := by
  have h := lower_regret_unsimplified ν hT hST π E θ hθ none v (Or.inl rfl)
  simpa [add_comm] using h

theorem lower_regret_candidate (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 2≤T) (hST : S.card≤T) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (v : S) :
    θ*((T:ℝ)-(∫ p, visits (T := T) π E θ (some v) v p ∂privateLaw ν S T))-1/512
      ≤expectedRegret (T := T) ν π E θ (some v) := by
  have h := lower_regret_unsimplified ν hT hST π E θ hθ (some v) v (Or.inr rfl)
  simp only [ite_true,mul_one] at h
  have ho : 0≤∫ p, outsideVisits (T := T) π E θ (some v) p ∂privateLaw ν S T :=
    integral_nonneg (outsideVisits_nonneg π E θ (some v))
  have hn : 0≤∫ p, switchTotal (T := T) π E θ (some v) p ∂privateLaw ν S T :=
    integral_nonneg (switchTotal_nonneg π E θ (some v))
  have hc : 0≤(1/4-θ)*(∫ p, outsideVisits (T := T) π E θ (some v) p ∂privateLaw ν S T) :=
    mul_nonneg (by linarith [hθ.2]) ho
  nlinarith

theorem lower_regret_parameters (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 2≤T) (hST : S.card≤T) (m : ℕ) (hm : 1≤m) (π : Learner ι Seed)
    (E : ι → ι → Prop) (v : S) :
    let θ := Parameters.theta T S.card m
    ((∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)+
      (1/4)*(∫ p, outsideVisits (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)-1/512
      ≤expectedRegret (T := T) ν π E θ (none : Coordinate S)) ∧
    (∀ u : S, θ*((T:ℝ)-(∫ p, visits (T := T) π E θ (some u) u p ∂privateLaw ν S T))-1/512
      ≤expectedRegret (T := T) ν π E θ (some u)) := by
  have hθ : 0≤Parameters.theta T S.card m ∧ Parameters.theta T S.card m≤1/64 :=
    ⟨Parameters.theta_nonneg T S.card m (by omega),Parameters.theta_le_one_sixty_four T S.card m hT hST hm⟩
  exact ⟨lower_regret_reference ν hT hST π E _ hθ v,
    fun u ↦ lower_regret_candidate ν hT hST π E _ hθ u⟩

end
end Tournament.Lower
