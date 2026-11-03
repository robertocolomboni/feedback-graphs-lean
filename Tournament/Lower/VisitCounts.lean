module

public import Tournament.Lower.RegretExecution
public import Tournament.Lower.ShiftCongestion
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Tournament.Lower

open MeasureTheory Model.MeasurableGame
open scoped Classical BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [MeasurableSpace Seed]
variable {S : Finset ι} {T : ℕ}

def visitCount (T : ℕ) (I : ℕ → ι) (v : ι) : ℕ :=
  ∑ t∈Finset.range T, if I t=v then 1 else 0

theorem member_indicators_total (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (∑ v : S, memberIndicator π E θ j v t p)+outsideIndicator π E θ j t p=1 := by
  simp only [memberIndicator]
  rw [Finset.sum_coe_sort S (fun v : ι ↦ if learnerAction π E θ j t.val p=v then (1:ℝ) else 0)]
  by_cases ha : learnerAction π E θ j t.val p∈S <;> simp [outsideIndicator,ha]

theorem visits_nonneg (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) : 0≤visits π E θ j v p := by
  apply Finset.sum_nonneg
  intro t _
  unfold memberIndicator
  split_ifs <;> norm_num

theorem visits_plus_outside (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (∑ v : S, visits π E θ j v p)+outsideVisits π E θ j p=(T:ℝ) := by
  unfold visits outsideVisits
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  simp only [member_indicators_total,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]

theorem visits_le_horizon (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) : visits π E θ j v p≤(T:ℝ) := by
  have hs : visits π E θ j v p≤∑ u : S, visits π E θ j u p :=
    Finset.single_le_sum (f := fun u ↦ visits π E θ j u p)
      (fun u _ ↦ visits_nonneg π E θ j u p) (Finset.mem_univ v)
  have hc := visits_plus_outside π E θ j p
  have ho := outsideVisits_nonneg π E θ j p
  linarith

theorem visits_eq_visitCount (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    visits π E θ j v p=(visitCount T (fun t ↦ learnerAction π E θ j t p) v.val:ℝ) := by
  unfold visits memberIndicator visitCount
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ if learnerAction π E θ j t p=v.val then (1:ℝ) else 0)]
  simp only [Nat.cast_sum,apply_ite,Nat.cast_zero,Nat.cast_one]

theorem outsideVisits_eq_outsideCount (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    outsideVisits π E θ j p=(outsideCount S T (fun t ↦ learnerAction π E θ j t p):ℝ) := by
  unfold outsideVisits outsideIndicator outsideCount
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ if learnerAction π E θ j t p∈S then (0:ℝ) else 1)]
  simp only [Nat.cast_sum,apply_ite,Nat.cast_zero,Nat.cast_one]

theorem outsideVisits_eq_source (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    outsideVisits π E θ j p=(T:ℝ)-∑ v : S, (visitCount T (fun t ↦ learnerAction π E θ j t p) v.val:ℝ) := by
  have h := visits_plus_outside π E θ j p
  simp only [visits_eq_visitCount] at h
  linarith

end
end Tournament.Lower
