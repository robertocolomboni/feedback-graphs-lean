module

public import Tournament.Computation.LinearProgramming.CompactOptimum
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Tournament.Computation.LinearProgramming.FiniteVertexSolver

open scoped BigOperators
open Matrix

def rowSelections (m : ℕ) : (n : ℕ) → List (Fin n → Fin m)
  | 0 => [Fin.elim0]
  | n+1 => (List.finRange m).flatMap fun i =>
      (rowSelections m n).map (Fin.cons i)

theorem mem_rowSelections (m n : ℕ) (s : Fin n → Fin m) : s ∈ rowSelections m n := by
  induction n with
  | zero =>
      have hs : s = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [rowSelections, hs]
  | succ n ih =>
      have hs : Fin.cons (s 0) (fun i => s i.succ) = s := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [rowSelections]
      apply List.mem_flatMap.mpr
      refine ⟨s 0, List.mem_finRange _, ?_⟩
      exact List.mem_map.mpr ⟨fun i => s i.succ, ih _, hs⟩

variable {m n : ℕ}

def feasible (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (q : Fin n → ℚ) : Prop :=
  ∀ i, ∑ j, (A i j : ℚ) * q j ≤ (b i : ℚ)

instance (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (q : Fin n → ℚ) :
    Decidable (feasible A b q) := inferInstanceAs (Decidable (∀ _i, _ ≤ _))

def objective (c : Fin n → ℤ) (q : Fin n → ℚ) : ℚ := ∑ j, (c j : ℚ) * q j

def candidate (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (s : Fin n → Fin m) : Option (Fin n → ℚ) :=
  let M := ActiveRows.selectedMatrix A s
  if M.det = 0 then none
  else
    let q := RationalVertexHeight.solution M (fun j => b (s j))
    if feasible A b q then some q else none

def candidates (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : List (Fin n → ℚ) :=
  (rowSelections m n).filterMap (candidate A b)

def solve (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) :
    Option (Fin n → ℚ) := (candidates A b).argmin (objective c)

theorem candidate_feasible (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (s : Fin n → Fin m) (q : Fin n → ℚ) (h : candidate A b s = some q) :
    feasible A b q := by
  dsimp only [candidate] at h
  split at h
  · cases h
  · split at h
    · rename_i hf
      cases h
      exact hf
    · cases h

theorem candidates_feasible (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (q : Fin n → ℚ) (h : q ∈ candidates A b) : feasible A b q := by
  obtain ⟨s, _, hs⟩ := List.mem_filterMap.mp h
  exact candidate_feasible A b s q hs

noncomputable def point (q : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (q j : ℝ))

theorem feasible_iff (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (q : Fin n → ℚ) :
    feasible A b q ↔ point q ∈ ActiveRows.integerPolyhedron A b := by
  simp only [feasible, ActiveRows.integerPolyhedron, ActiveRows.polyhedron,
    Set.mem_ofPred_eq, ActiveRows.integerRow, point, PiLp.inner_apply, Real.inner_apply]
  constructor <;> intro h i
  · have hi := h i
    exact_mod_cast hi
  · have hi := h i
    exact_mod_cast hi

noncomputable def realObjective (c : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ∑ j, (c j : ℝ) • EuclideanSpace.proj j

theorem realObjective_apply (c : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    realObjective c x = ∑ j, (c j : ℝ) * x j := by
  simp [realObjective]

theorem objective_cast (c : Fin n → ℤ) (q : Fin n → ℚ) :
    (objective c q : ℝ) = realObjective c (point q) := by
  simp [objective, realObjective_apply, point]

theorem extreme_mem_candidates (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (ActiveRows.integerPolyhedron A b).extremePoints ℝ) :
    ∃ q ∈ candidates A b, point q = x := by
  obtain ⟨s, hdet, hsystem⟩ := ActiveRows.exists_active_nonsingular_subsystem A b x hx
  let q := RationalVertexHeight.solution (ActiveRows.selectedMatrix A s) (fun j => b (s j))
  have he := RationalVertexHeight.real_solution_unique (ActiveRows.selectedMatrix A s)
    (fun j => b (s j)) hdet (fun j => x j) hsystem
  have hp : point q = x := by
    ext j
    exact (congrFun he j).symm
  have hq : feasible A b q := (feasible_iff A b q).mpr (hp.symm ▸ hx.1)
  refine ⟨q, List.mem_filterMap.mpr ⟨s, mem_rowSelections m n s, ?_⟩, hp⟩
  simp only [candidate, hdet, ↓reduceIte]
  exact ite_eq_left hq

theorem solve_correct (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ)
    (hcompact : IsCompact (ActiveRows.integerPolyhedron A b))
    (hne : (ActiveRows.integerPolyhedron A b).Nonempty) :
    ∃ q, solve A b c = some q ∧ feasible A b q ∧
      ∀ y ∈ ActiveRows.integerPolyhedron A b, realObjective c (point q) ≤ realObjective c y := by
  obtain ⟨x, hx, hmin⟩ := CompactOptimum.exists_extreme_minimizer _ hcompact hne (realObjective c)
  obtain ⟨q, hq, hqx⟩ := extreme_mem_candidates A b x hx
  cases hs : solve A b c with
  | none =>
      have he : candidates A b = [] := List.argmin_eq_none.mp hs
      simp [he] at hq
  | some r =>
      have hr : r ∈ (candidates A b).argmin (objective c) := hs
      refine ⟨r, rfl, candidates_feasible A b r (List.argmin_mem hr), ?_⟩
      intro y hy
      have hle := List.le_of_mem_argmin hq hr
      have hreal : realObjective c (point r) ≤ realObjective c (point q) := by
        rw [← objective_cast, ← objective_cast]
        exact_mod_cast hle
      exact hreal.trans (hqx ▸ hmin y hy)

end Tournament.Computation.LinearProgramming.FiniteVertexSolver
