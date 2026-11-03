module

public import Tournament.Graphs.Observing
public import Tournament.Model.Minimax
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Tournament.Lower.Unobservable

open MeasureTheory Model MeasurableGame
open scoped Classical BigOperators
noncomputable section

variable {ι Seed : Type*}

def loss (i j : ι) (high : Bool) : ℕ → ι → ℝ := fun _ a ↦
  if a=i then (if high then 1 else 0) else if a=j then 1/2 else 1

theorem loss_bounds (i j : ι) (high : Bool) (t : ℕ) (a : ι) :
    0≤loss i j high t a ∧ loss i j high t a≤1 := by
  unfold loss
  split_ifs <;> norm_num

theorem same_feedback (E : ι → ι → Prop) (i j : ι) (hInvisible : ∀ a, ¬E a i)
    (a : ι) (t : ℕ) :
    graphRecord E a (loss i j false t)=graphRecord E a (loss i j true t) := by
  funext v
  by_cases hEv : E a v
  · have hvi : v≠i := fun h ↦ hInvisible a (h ▸ hEv)
    simp only [graphRecord,ite_eq_left hEv,loss,ite_eq_right hvi]
  · simp only [graphRecord,ite_eq_right hEv]

theorem loss_sum_ge_one (i j a : ι) (t : ℕ) :
    (1:ℝ)≤loss i j false t a+loss i j true t a := by
  unfold loss
  split_ifs <;> norm_num at *

variable [Fintype ι] [Nonempty ι]

theorem path_regrets_sum (T : ℕ) (i j : ι) (hij : i≠j) (X : ℕ → ι) :
    (T:ℝ)/2≤pathRegret T (loss i j false) X+pathRegret T (loss i j true) X := by
  have hBest0 := bestFixedLoss_le T (loss i j false) i
  have hBest1 := bestFixedLoss_le T (loss i j true) j
  have hFixed0 : fixedLoss T (loss i j false) i=0 := by simp [fixedLoss,loss]
  have hFixed1 : fixedLoss T (loss i j true) j=(T:ℝ)/2 := by simp [fixedLoss,loss,hij.symm]; ring
  rw [hFixed0] at hBest0
  rw [hFixed1] at hBest1
  have hPlayed : (T:ℝ)≤accumulatedLoss T (loss i j false) X+accumulatedLoss T (loss i j true) X := by
    calc
      _ = ∑ _t∈Finset.range T, (1:ℝ) := by simp
      _ ≤ ∑ t∈Finset.range T, (loss i j false t (X t)+loss i j true t (X t)) :=
        Finset.sum_le_sum (fun t _ ↦ loss_sum_ge_one i j (X t) t)
      _ = _ := Finset.sum_add_distrib
  have hSwitch : (0:ℝ)≤(switchCount T X:ℝ) := by positivity
  unfold pathRegret
  linarith

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Seed]

omit [Fintype ι] [Nonempty ι] [DiscreteMeasurableSpace ι] in
theorem actions_equal (π : Learner ι Seed) (E : ι → ι → Prop) (i j : ι)
    (hInvisible : ∀ a, ¬E a i) (t : ℕ) (seed : Seed) :
    deterministicAction π E (loss i j false) t seed=deterministicAction π E (loss i j true) t seed := by
  apply action_equal_of_past_feedback π E
    (fun n (_ : Unit) ↦ loss i j false n) (fun n (_ : Unit) ↦ loss i j true n) t (seed,()) (seed,()) rfl
  intro s _
  exact same_feedback E i j hInvisible _ s

theorem two_environment_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ)
    (π : Learner ι Seed) (E : ι → ι → Prop) (i j : ι) (hij : i≠j) (hInvisible : ∀ a, ¬E a i) :
    (T:ℝ)/2≤deterministicExpectedRegret T ν π E (loss i j false)+
      deterministicExpectedRegret T ν π E (loss i j true) := by
  have hPoint (seed : Seed) : (T:ℝ)/2≤deterministicPathRegret T π E (loss i j false) seed+
      deterministicPathRegret T π E (loss i j true) seed := by
    have hPaths : (fun t ↦ deterministicAction π E (loss i j true) t seed)=
        fun t ↦ deterministicAction π E (loss i j false) t seed :=
      funext (fun t ↦ (actions_equal π E i j hInvisible t seed).symm)
    unfold deterministicPathRegret
    rw [hPaths]
    exact path_regrets_sum T i j hij _
  have hI0 := deterministicPathRegret_integrable T ν π E (loss i j false) (loss_bounds i j false)
  have hI1 := deterministicPathRegret_integrable T ν π E (loss i j true) (loss_bounds i j true)
  have h := integral_mono (μ := ν) (integrable_const ((T:ℝ)/2)) (hI0.add hI1) hPoint
  change (∫ _ : Seed, (T:ℝ)/2 ∂ν)≤∫ seed,
    deterministicPathRegret T π E (loss i j false) seed+
      deterministicPathRegret T π E (loss i j true) seed ∂ν at h
  rw [integral_const,integral_add hI0 hI1] at h
  simpa only [probReal_univ,one_smul,deterministicExpectedRegret] using h

theorem lower_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hNot : ¬Observable E) (hK : 2≤Fintype.card ι) :
    ∃ L : ℕ → ι → ℝ, BoundedSequence L ∧ (T:ℝ)/4≤deterministicExpectedRegret T ν π E L := by
  have hInvisible : ∃ i, ∀ a, ¬E a i := by simpa only [Observable,not_forall,not_exists] using hNot
  obtain ⟨i,hi⟩ := hInvisible
  let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨j,hji⟩ := exists_ne i
  have h := two_environment_bound ν T π E i j hji.symm hi
  by_cases hLow : (T:ℝ)/4≤deterministicExpectedRegret T ν π E (loss i j false)
  · exact ⟨loss i j false,loss_bounds i j false,hLow⟩
  · exact ⟨loss i j true,loss_bounds i j true,by linarith⟩

end
end Tournament.Lower.Unobservable

namespace Tournament.Lower.Unobservable

open Model.MeasurableGame

universe u v
variable {ι : Type u} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]

theorem minimax_bounds (T : ℕ) (E : ι → ι → Prop) (hNot : ¬Observable E) (hK : 2≤Fintype.card ι) :
    (T:ℝ)/4≤minimax.{u,v} T E ∧ minimax.{u,v} T E≤(T:ℝ) := by
  refine ⟨?_,minimax_le_horizon T E⟩
  apply le_minimax
  intro σ
  let := σ.seedSpace
  let := σ.probability
  obtain ⟨L,hL,hReg⟩ := lower_bound σ.law T σ.learner E hNot hK
  exact ⟨L,hL,hReg⟩

end Tournament.Lower.Unobservable
