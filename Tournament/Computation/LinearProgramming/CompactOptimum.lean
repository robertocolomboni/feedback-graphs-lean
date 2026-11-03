module

public import Tournament.Computation.LinearProgramming.ActiveRows
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

namespace Tournament.Computation.LinearProgramming.CompactOptimum

theorem exists_extreme_minimizer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hcompact : IsCompact C) (hne : C.Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x, x ∈ C.extremePoints ℝ ∧ ∀ y ∈ C, f x ≤ f y := by
  let S := (-f).toExposed C
  have hface : IsExposed ℝ C S := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hne f.continuous.continuousOn
  have hS : S.Nonempty := by
    refine ⟨z, hz, ?_⟩
    intro y hy
    change -f y ≤ -f z
    exact neg_le_neg (hmin hy)
  obtain ⟨x, hx⟩ := (hface.isCompact hcompact).extremePoints_nonempty hS
  refine ⟨x, hface.isExtreme.extremePoints_subset_extremePoints hx, ?_⟩
  intro y hy
  have hxy : -f y ≤ -f x := hx.1.2 y hy
  exact neg_le_neg_iff.mp hxy

theorem integerPolyhedron_isClosed {ι : Type*} {n : ℕ}
    (A : ι → Fin n → ℤ) (b : ι → ℤ) : IsClosed (ActiveRows.integerPolyhedron A b) := by
  simp only [ActiveRows.integerPolyhedron, ActiveRows.polyhedron, Set.ofPred_forall]
  exact isClosed_iInter fun _ => isClosed_le (continuous_const.inner continuous_id) continuous_const

end Tournament.Computation.LinearProgramming.CompactOptimum
