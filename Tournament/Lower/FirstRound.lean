module

public import Tournament.Model.DeterministicExecution
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

namespace Tournament.Lower

open MeasureTheory Model.MeasurableGame
open scoped Classical BigOperators

noncomputable section

variable {ι Seed : Type*}

def oneRoundLoss (best : ι) (t : ℕ) (a : ι) : ℝ := if t=0 then if a=best then 0 else 1 else 0

theorem oneRoundLoss_bounds (best : ι) (t : ℕ) (a : ι) :
    0≤oneRoundLoss best t a ∧ oneRoundLoss best t a≤1 := by
  unfold oneRoundLoss
  split_ifs <;> norm_num

theorem oneRoundLoss_accumulated (T : ℕ) (hT : 1≤T) (best : ι) (I : ℕ → ι) :
    Model.accumulatedLoss T (oneRoundLoss best) I=(if I 0=best then (0:ℝ) else 1) := by
  unfold Model.accumulatedLoss
  rw [Finset.sum_eq_single 0]
  · simp only [oneRoundLoss,ite_true]
  · intro t _ ht
    simp only [oneRoundLoss,ite_eq_right ht]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

variable [Fintype ι] [Nonempty ι]

theorem oneRoundLoss_best (T : ℕ) (best : ι) : Model.bestFixedLoss T (oneRoundLoss best)=0 := by
  have h0 := Model.bestFixedLoss_nonneg T (oneRoundLoss best) (fun t _ a ↦ (oneRoundLoss_bounds best t a).1)
  have h1 := Model.bestFixedLoss_le T (oneRoundLoss best) best
  have hbest : Model.fixedLoss T (oneRoundLoss best) best=0 := by simp [Model.fixedLoss,oneRoundLoss]
  rw [hbest] at h1
  exact le_antisymm h1 h0

theorem oneRoundLoss_regret_lower (T : ℕ) (hT : 1≤T) (best : ι) (I : ℕ → ι) :
    (if I 0=best then (0:ℝ) else 1)≤Model.pathRegret T (oneRoundLoss best) I := by
  unfold Model.pathRegret
  rw [oneRoundLoss_best,oneRoundLoss_accumulated T hT]
  have hN : 0≤(Model.switchCount T I:ℝ) := by positivity
  linarith

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Seed]

theorem two_action_mixture_regret (T : ℕ) (hT : 1≤T) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (hab : a≠b) :
    (1:ℝ)/2≤(deterministicExpectedRegret T ν π E (oneRoundLoss a)+
      deterministicExpectedRegret T ν π E (oneRoundLoss b))/2 := by
  have hPoint : ∀ seed, (1:ℝ)≤deterministicPathRegret T π E (oneRoundLoss a) seed+
      deterministicPathRegret T π E (oneRoundLoss b) seed := by
    intro seed
    have hA := oneRoundLoss_regret_lower T hT a (fun n ↦ deterministicAction π E (oneRoundLoss a) n seed)
    have hB := oneRoundLoss_regret_lower T hT b (fun n ↦ deterministicAction π E (oneRoundLoss b) n seed)
    have hfirst (loss : ℕ → ι → ℝ) : deterministicAction π E loss 0 seed=
        π.choose 0 (seed,fun q ↦ Fin.elim0 q) := rfl
    rw [hfirst] at hA hB
    have hInd : (1:ℝ)≤(if π.choose 0 (seed,fun q ↦ Fin.elim0 q)=a then 0 else 1)+
        (if π.choose 0 (seed,fun q ↦ Fin.elim0 q)=b then 0 else 1) := by
      by_cases ha : π.choose 0 (seed,fun q ↦ Fin.elim0 q)=a
      · have hb : π.choose 0 (seed,fun q ↦ Fin.elim0 q)≠b := fun hb ↦ hab (ha.symm.trans hb)
        simp only [ite_eq_left ha,ite_eq_right hb,zero_add,le_rfl]
      · simp only [ite_eq_right ha]
        split_ifs <;> norm_num
    change _≤deterministicPathRegret T π E (oneRoundLoss a) seed at hA
    change _≤deterministicPathRegret T π E (oneRoundLoss b) seed at hB
    linarith
  have hiA := deterministicPathRegret_integrable T ν π E (oneRoundLoss a) (oneRoundLoss_bounds a)
  have hiB := deterministicPathRegret_integrable T ν π E (oneRoundLoss b) (oneRoundLoss_bounds b)
  have h := integral_mono (integrable_const (1:ℝ)) (hiA.add hiB) hPoint
  change (∫ _ : Seed, (1:ℝ) ∂ν)≤∫ seed, deterministicPathRegret T π E (oneRoundLoss a) seed+
    deterministicPathRegret T π E (oneRoundLoss b) seed ∂ν at h
  rw [integral_const,integral_add hiA hiB] at h
  simp only [probReal_univ,smul_eq_mul,one_mul] at h
  change (1:ℝ)/2≤((∫ seed, deterministicPathRegret T π E (oneRoundLoss a) seed ∂ν)+
    (∫ seed, deterministicPathRegret T π E (oneRoundLoss b) seed ∂ν))/2
  linarith

theorem exists_oblivious_loss_half (T : ℕ) (hT : 1≤T) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (a b : ι) (hab : a≠b) :
    ∃ loss : ℕ → ι → ℝ, (∀ t i, 0≤loss t i ∧ loss t i≤1) ∧
      (1:ℝ)/2≤deterministicExpectedRegret T ν π E loss := by
  have h := two_action_mixture_regret T hT ν π E a b hab
  by_cases hA : (1:ℝ)/2≤deterministicExpectedRegret T ν π E (oneRoundLoss a)
  · exact ⟨oneRoundLoss a,oneRoundLoss_bounds a,hA⟩
  · exact ⟨oneRoundLoss b,oneRoundLoss_bounds b,by linarith⟩

end
end Tournament.Lower
