module

public import Tournament.Lower.GaussianProduct

@[expose] public section

namespace Tournament.Lower.GaussianProduct

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

variable {C : Type*} [Fintype C]

omit [Fintype C] in
theorem walk_measurable (T : ℕ) (c : C) (t : ℕ) : Measurable (walk (T := T) c t) := by
  unfold walk Dyadic.finiteWalk increment
  fun_prop

def walkIndices (T : ℕ) (c : C) (t : ℕ) : Finset (Fin T × C) :=
  (Dyadic.incrementSet T t).image (fun j ↦ (j,c))

omit [Fintype C] in
theorem walkIndices_disjoint (T : ℕ) (c d : C) (hcd : c≠d) (s t : ℕ) :
    Disjoint (walkIndices T c s) (walkIndices T d t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hp
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hq
  exact hcd (congrArg Prod.snd (hj.trans hk.symm))

omit [Fintype C] in
theorem walk_sum (T : ℕ) (c : C) (t : ℕ) :
    (fun ω : Space T C ↦ ∑ p : walkIndices T c t, ω p)=walk c t := by
  funext ω
  rw [Finset.sum_coe_sort (walkIndices T c t) (fun p ↦ ω p)]
  unfold walkIndices
  rw [Finset.sum_image (fun j _ k _ h ↦ congrArg Prod.fst h)]
  rfl

theorem walks_independent (T : ℕ) (v : ℝ≥0) (c d : C) (hcd : c≠d) (s t : ℕ) :
    IndepFun (walk c s) (walk d t) (law T v) := by
  have hind := iIndepFun.indepFun_finset (walkIndices T c s) (walkIndices T d t)
    (walkIndices_disjoint T c d hcd s t) (all_increments_independent T v)
    (fun p ↦ measurable_pi_apply p)
  have h := hind.comp (φ := fun f : walkIndices T c s → ℝ ↦ ∑ p, f p)
    (ψ := fun f : walkIndices T d t → ℝ ↦ ∑ p, f p) (by fun_prop) (by fun_prop)
  simpa only [Function.comp_def,walk_sum] using h

theorem signed_walk_law (T : ℕ) (v : ℝ≥0) (c : C) (t : ℕ)
    (sign : ℝ) (hsign : sign^2=1) :
    HasLaw (fun ω ↦ sign*walk c t ω)
      (gaussianReal 0 ((Dyadic.incrementSet T t).card • v)) (law T v) := by
  have h := gaussianReal_const_mul (walk_law T v c t) sign
  simpa [hsign] using h

theorem common_signed_walk_law (T : ℕ) (v : ℝ≥0) (c d : C) (hcd : c≠d) (t : ℕ)
    (sign : ℝ) (hsign : sign^2=1) :
    HasLaw (fun ω ↦ walk c t ω+sign*walk d t ω)
      (gaussianReal 0 (2*((Dyadic.incrementSet T t).card • v))) (law T v) := by
  have hind := (walks_independent T v c d hcd t t).comp (φ := id)
    (ψ := fun x : ℝ ↦ sign*x) measurable_id (by fun_prop)
  have hl := signed_walk_law T v d t sign hsign
  refine ⟨(walk_law T v c t).aemeasurable.add hl.aemeasurable,?_⟩
  have h := gaussianReal_add_gaussianReal_of_indepFun hind (walk_law T v c t) hl
  have heq : id ∘ walk (T := T) c t+(fun x : ℝ ↦ sign*x) ∘ walk d t=
      (fun ω : Space T C ↦ walk c t ω+sign*walk d t ω) := rfl
  rw [heq] at h
  simpa only [zero_add,two_mul] using h

end
end Tournament.Lower.GaussianProduct
