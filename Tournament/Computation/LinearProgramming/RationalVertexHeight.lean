module

public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Tournament.Computation.LinearProgramming.RationalVertexHeight

open Matrix

variable {n : ℕ}

def rationalMatrix (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  A.map fun z => (z : ℚ)

def rationalVector (b : Fin n → ℤ) : Fin n → ℚ := fun i => (b i : ℚ)

def solution (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) : Fin n → ℚ :=
  fun i => (Matrix.cramer A b i : ℚ) / (A.det : ℚ)

theorem rationalMatrix_det (A : Matrix (Fin n) (Fin n) ℤ) :
    (rationalMatrix A).det = (A.det : ℚ) := (Int.cast_det A).symm

theorem cast_cramer (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) :
    (Matrix.cramer A b i : ℚ) = Matrix.cramer (rationalMatrix A) (rationalVector b) i := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, Int.cast_det, Matrix.map_updateCol]
  rfl

theorem solution_eq_scaled_cramer (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) :
    solution A b = (A.det : ℚ)⁻¹ • Matrix.cramer (rationalMatrix A) (rationalVector b) := by
  ext i
  simp only [solution, Pi.smul_apply, smul_eq_mul, cast_cramer, div_eq_mul_inv, mul_comm]

theorem solution_correct (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hA : A.det ≠ 0) : rationalMatrix A *ᵥ solution A b = rationalVector b := by
  have hAq : (A.det : ℚ) ≠ 0 := by exact_mod_cast hA
  rw [solution_eq_scaled_cramer, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    rationalMatrix_det, smul_smul, inv_mul_cancel₀ hAq, one_smul]

theorem real_solution_correct (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hA : A.det ≠ 0) :
    (A.map fun z => (z : ℝ)) *ᵥ (fun i => (solution A b i : ℝ)) =
      fun i => (b i : ℝ) := by
  have h := solution_correct A b hA
  ext i
  have hi := congrArg (fun v : Fin n → ℚ => (v i : ℝ)) h
  simpa [rationalMatrix, rationalVector, Matrix.mulVec, dotProduct] using hi

theorem real_solution_unique (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hA : A.det ≠ 0) (x : Fin n → ℝ)
    (hx : (A.map fun z => (z : ℝ)) *ᵥ x = fun i => (b i : ℝ)) :
    x = fun i => (solution A b i : ℝ) := by
  apply Matrix.mulVec_injective_of_det_ne_zero (M := A.map fun z => (z : ℝ))
  · rw [← Int.cast_det]
    exact_mod_cast hA
  · rw [hx, real_solution_correct A b hA]

end Tournament.Computation.LinearProgramming.RationalVertexHeight
