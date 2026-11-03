module

public import Tournament.Lower.DyadicGaussian

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

theorem independent_gaussian_sum {Ω J : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [DecidableEq J]
    (X : J → Ω → ℝ) {v : ℝ≥0}
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 v) μ) (hIndep : iIndepFun X μ)
    (s : Finset J) : HasLaw (∑ j∈s, X j) (gaussianReal 0 (s.card • v)) μ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,Finset.card_empty,zero_nsmul,gaussianReal_zero_var]
    exact hasLaw_dirac_of_ae_eq (Filter.EventuallyEq.rfl)
  | @insert i s hi ih =>
    have hind := (hIndep.indepFun_finsetSum_of_notMem₀ (fun j ↦ (hLaw j).aemeasurable) hi).symm
    have hmap := gaussianReal_add_gaussianReal_of_indepFun hind (hLaw i) ih
    refine ⟨?_,?_⟩
    · rw [Finset.sum_insert hi]
      exact (hLaw i).aemeasurable.add ih.aemeasurable
    · simpa only [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,add_nsmul,one_nsmul,
        zero_add,add_comm] using hmap

namespace GaussianProduct

abbrev Space (T : ℕ) (C : Type*) := Fin T × C → ℝ

variable {C : Type*} [Fintype C]

def law (T : ℕ) (v : ℝ≥0) : Measure (Space T C) :=
  Measure.pi (fun _ : Fin T × C ↦ gaussianReal 0 v)

instance law_probability (T : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (law (C := C) T v) := by
  unfold law
  infer_instance

def increment {T : ℕ} (c : C) (j : Fin T) (ω : Space T C) : ℝ := ω (j,c)

omit [Fintype C] in
theorem increment_measurable {T : ℕ} (c : C) (j : Fin T) : Measurable (increment c j) :=
  measurable_pi_apply (j,c)

theorem increment_law (T : ℕ) (v : ℝ≥0) (c : C) (j : Fin T) :
    HasLaw (increment c j) (gaussianReal 0 v) (law T v) :=
  (measurePreserving_eval (fun _ : Fin T × C ↦ gaussianReal 0 v) (j,c)).hasLaw

theorem all_increments_independent (T : ℕ) (v : ℝ≥0) :
    iIndepFun (fun p : Fin T × C ↦ fun ω : Space T C ↦ ω p) (law T v) :=
  iIndepFun_pi (fun _ ↦ aemeasurable_id)

theorem increments_independent (T : ℕ) (v : ℝ≥0) (c : C) :
    iIndepFun (increment (T := T) c) (law T v) := by
  change iIndepFun (fun j : Fin T ↦ fun ω : Space T C ↦ ω (j,c)) _
  exact iIndepFun.precomp (g := fun j : Fin T ↦ (j,c))
    (fun _ _ h ↦ congrArg Prod.fst h) (all_increments_independent (C := C) T v)

def walk {T : ℕ} (c : C) (t : ℕ) : Space T C → ℝ := Dyadic.finiteWalk (increment c) t

omit [Fintype C] in
theorem walk_zero {T : ℕ} (c : C) : walk (T := T) c 0=0 := Dyadic.finiteWalk_zero _

omit [Fintype C] in
theorem walk_parent {T : ℕ} (c : C) (t : ℕ) (ht : 0<t) (htT : t≤T) :
    walk (T := T) c t=walk c (Dyadic.parent t)+increment c ⟨t-1,by omega⟩ :=
  Dyadic.finiteWalk_parent _ t ht htT

theorem walk_law (T : ℕ) (v : ℝ≥0) (c : C) (t : ℕ) :
    HasLaw (walk c t) (gaussianReal 0 ((Dyadic.incrementSet T t).card • v)) (law T v) := by
  have h := independent_gaussian_sum (increment c) (increment_law T v c)
    (increments_independent T v c) (Dyadic.incrementSet T t)
  have heq : (∑ j∈Dyadic.incrementSet T t, increment c j)=walk c t := by
    funext ω
    simp only [walk,Dyadic.finiteWalk,Finset.sum_apply]
  rw [heq] at h
  exact h

theorem walk_mean (T : ℕ) (v : ℝ≥0) (c : C) (t : ℕ) :
    ∫ ω, walk c t ω ∂law T v=0 := by
  rw [(walk_law T v c t).integral_eq,integral_id_gaussianReal]

theorem walk_variance (T : ℕ) (v : ℝ≥0) (c : C) (t : ℕ) (hT : 0<T) (htT : t≤T) :
    Var[walk c t;law T v]≤Dyadic.upsilon T*(v:ℝ) :=
  Dyadic.gaussian_walk_variance (increment c) (increment_law T v c)
    (increments_independent T v c) t hT htT

end GaussianProduct
end
end Tournament.Lower
