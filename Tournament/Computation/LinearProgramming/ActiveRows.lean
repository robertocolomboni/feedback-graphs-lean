module

public import Tournament.Computation.LinearProgramming.RationalVertexHeight
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace Tournament.Computation.LinearProgramming.ActiveRows

open scoped InnerProductSpace BigOperators
open Matrix

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polyhedron (A : ι → E) (b : ι → ℝ) : Set E :=
  {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i}

def activeRows (A : ι → E) (b : ι → ℝ) (x : E) : Set E :=
  A '' {i | ⟪A i, x⟫_ℝ = b i}

theorem exists_positive_lower_bound (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ r i := by
  classical
  have aux : ∀ s : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ r i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min (r i) ε, lt_min (hr i) hε, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound j hj)
  obtain ⟨ε, hε, hbound⟩ := aux Finset.univ
  exact ⟨ε, hε, fun i => hbound i (Finset.mem_univ i)⟩

theorem exists_feasible_perturbation (A : ι → E) (b : ι → ℝ) (x y : E)
    (hx : x ∈ polyhedron A b)
    (hy : ∀ i, ⟪A i, x⟫_ℝ = b i → ⟪A i, y⟫_ℝ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ x + ε • y ∈ polyhedron A b ∧
      x - ε • y ∈ polyhedron A b := by
  classical
  let r : ι → ℝ := fun i =>
    if ⟪A i, x⟫_ℝ = b i then 1 else (b i - ⟪A i, x⟫_ℝ) / (|⟪A i, y⟫_ℝ| + 1)
  have hr : ∀ i, 0 < r i := by
    intro i
    by_cases hi : ⟪A i, x⟫_ℝ = b i
    · simp [r, hi]
    · have hslack : 0 < b i - ⟪A i, x⟫_ℝ := by
        have hxi := hx i
        rcases lt_or_eq_of_le hxi with hlt | heq
        · linarith
        · exact (hi heq).elim
      dsimp [r]
      rw [ite_eq_right hi]
      exact div_pos hslack (by positivity)
  obtain ⟨ε, hε, hbound⟩ := exists_positive_lower_bound r hr
  have hslack : ∀ i, ε * |⟪A i, y⟫_ℝ| ≤ b i - ⟪A i, x⟫_ℝ := by
    intro i
    by_cases hi : ⟪A i, x⟫_ℝ = b i
    · rw [hy i hi, abs_zero, mul_zero, hi, sub_self]
    · have hri := hbound i
      dsimp [r] at hri
      rw [ite_eq_right hi] at hri
      have hden : 0 < |⟪A i, y⟫_ℝ| + 1 := by positivity
      have hm := (le_div_iff₀ hden).mp hri
      nlinarith
  refine ⟨ε, hε, ?_, ?_⟩
  · intro i
    rw [inner_add_right, inner_smul_right]
    have hm := mul_le_mul_of_nonneg_left (le_abs_self ⟪A i, y⟫_ℝ) hε.le
    linarith [hslack i]
  · intro i
    rw [inner_sub_right, inner_smul_right]
    have hm := mul_le_mul_of_nonneg_left (neg_le_abs ⟪A i, y⟫_ℝ) hε.le
    linarith [hslack i]

theorem active_annihilator_eq_zero (A : ι → E) (b : ι → ℝ) (x y : E)
    (hx : x ∈ (polyhedron A b).extremePoints ℝ)
    (hy : ∀ i, ⟪A i, x⟫_ℝ = b i → ⟪A i, y⟫_ℝ = 0) : y = 0 := by
  obtain ⟨ε, hε, hplus, hminus⟩ := exists_feasible_perturbation A b x y hx.1 hy
  have heq := hx.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) x (ε • y))
  have hzero : ε • y = 0 := by
    simpa using congrArg (fun z => z - x) heq
  exact (smul_eq_zero.mp hzero).resolve_left hε.ne'

theorem active_span_eq_top [FiniteDimensional ℝ E]
    (A : ι → E) (b : ι → ℝ) (x : E)
    (hx : x ∈ (polyhedron A b).extremePoints ℝ) :
    Submodule.span ℝ (activeRows A b x) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro y hy
  change y = 0
  apply active_annihilator_eq_zero A b x y hx
  intro i hi
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (show A i ∈ activeRows A b x from ⟨i, hi, rfl⟩)) hy

theorem exists_independent_active_rows [FiniteDimensional ℝ E]
    (A : ι → E) (b : ι → ℝ) (x : E)
    (hx : x ∈ (polyhedron A b).extremePoints ℝ) :
    ∃ select : Fin (Module.finrank ℝ E) → ι,
      (∀ j, ⟪A (select j), x⟫_ℝ = b (select j)) ∧
      LinearIndependent ℝ (fun j => A (select j)) := by
  classical
  have hspan := active_span_eq_top A b x hx
  let B := Module.Basis.ofSpan (le_of_eq hspan.symm)
  let := FiniteDimensional.fintypeBasisIndex B
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  let Bfin := B.reindex e
  have hmem : ∀ j, Bfin j ∈ activeRows A b x := by
    intro j
    apply Module.Basis.ofSpan_subset (le_of_eq hspan.symm)
    exact ⟨e.symm j, (Module.Basis.reindex_apply B e j).symm⟩
  change ∀ j, ∃ i, ⟪A i, x⟫_ℝ = b i ∧ A i = Bfin j at hmem
  choose select hactive hrow using hmem
  refine ⟨select, hactive, ?_⟩
  have hfamily : (fun j => A (select j)) = Bfin := funext hrow
  rw [hfamily]
  exact Bfin.linearIndependent

section Integer

variable {n : ℕ}

noncomputable def integerRow (A : ι → Fin n → ℤ) (i : ι) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (A i j : ℝ))

noncomputable def integerPolyhedron (A : ι → Fin n → ℤ) (b : ι → ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) := polyhedron (integerRow A) (fun i => (b i : ℝ))

def selectedMatrix (A : ι → Fin n → ℤ) (select : Fin n → ι) : Matrix (Fin n) (Fin n) ℤ :=
  fun j k => A (select j) k

theorem exists_active_nonsingular_subsystem
    (A : ι → Fin n → ℤ) (b : ι → ℤ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (integerPolyhedron A b).extremePoints ℝ) :
    ∃ select : Fin n → ι, (selectedMatrix A select).det ≠ 0 ∧
      ((selectedMatrix A select).map fun z => (z : ℝ)) *ᵥ (fun k => x k) =
        fun j => (b (select j) : ℝ) := by
  classical
  have hselected : ∃ select : Fin n → ι,
      (∀ j, ⟪integerRow A (select j), x⟫_ℝ = (b (select j) : ℝ)) ∧
      LinearIndependent ℝ (fun j => integerRow A (select j)) := by
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
      finrank_euclideanSpace_fin
    have h := exists_independent_active_rows (integerRow A) (fun i => (b i : ℝ)) x hx
    rw [hdim] at h
    exact h
  obtain ⟨select, hactive, hind⟩ := hselected
  have hlin : LinearIndependent ℝ
      (fun j : Fin n => fun k : Fin n => (A (select j) k : ℝ)) := by
    have hmap := hind.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
    simpa [Function.comp_def, integerRow] using hmap
  have hunit : IsUnit ((selectedMatrix A select).map fun z => (z : ℝ)) :=
    Matrix.linearIndependent_row_iff_isUnit.mp hlin
  have hdetreal : ((selectedMatrix A select).map fun z => (z : ℝ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hdet : (selectedMatrix A select).det ≠ 0 := by
    rw [← Int.cast_det] at hdetreal
    exact_mod_cast hdetreal
  refine ⟨select, hdet, ?_⟩
  ext j
  simpa [integerRow, selectedMatrix, PiLp.inner_apply, Matrix.mulVec, dotProduct,
    mul_comm] using hactive j

end Integer

end Tournament.Computation.LinearProgramming.ActiveRows
