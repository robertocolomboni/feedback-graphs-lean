module

public import Tournament.Upper.Resolvent
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical Matrix

noncomputable section

variable {ι : Type*} [Fintype ι]

def scaledGeneratorMatrix (H : HoldingFamily ι) : Matrix ι ι ℝ :=
  fun i j ↦ Real.sqrt (H.sampling i)*H.generatorMatrix i j/Real.sqrt (H.sampling j)

theorem sqrt_sampling_pos (H : HoldingFamily ι) (i : ι) : 0 < Real.sqrt (H.sampling i) :=
  Real.sqrt_pos.mpr (H.sampling_pos i)

theorem scaledGeneratorMatrix_symmetric (H : HoldingFamily ι) (i j : ι) :
    H.scaledGeneratorMatrix i j=H.scaledGeneratorMatrix j i := by
  unfold scaledGeneratorMatrix
  apply (div_eq_div_iff (ne_of_gt (H.sqrt_sampling_pos j)) (ne_of_gt (H.sqrt_sampling_pos i))).mpr
  calc
    _ = (Real.sqrt (H.sampling i)*Real.sqrt (H.sampling i))*H.generatorMatrix i j := by ring
    _ = H.sampling i*H.generatorMatrix i j := by rw [Real.mul_self_sqrt (H.sampling.nonneg i)]
    _ = H.sampling j*H.generatorMatrix j i := H.weighted_generatorMatrix_symmetric i j
    _ = (Real.sqrt (H.sampling j)*Real.sqrt (H.sampling j))*H.generatorMatrix j i := by
      rw [Real.mul_self_sqrt (H.sampling.nonneg j)]
    _ = _ := by ring

theorem scaledGeneratorMatrix_isHermitian (H : HoldingFamily ι) : H.scaledGeneratorMatrix.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial]
  exact H.scaledGeneratorMatrix_symmetric j i

theorem scaledGeneratorMatrix_apply (H : HoldingFamily ι) (g : ι → ℝ) (i : ι) :
    (H.scaledGeneratorMatrix *ᵥ g) i =
      Real.sqrt (H.sampling i)*H.generator (fun j ↦ g j/Real.sqrt (H.sampling j)) i := by
  rw [← H.generatorMatrix_apply]
  change (∑ j, (Real.sqrt (H.sampling i)*H.generatorMatrix i j/Real.sqrt (H.sampling j))*g j) = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ by ring)

def unscaleEquiv (H : HoldingFamily ι) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun g i := g i/Real.sqrt (H.sampling i)
  invFun f i := Real.sqrt (H.sampling i)*f i
  left_inv g := by
    funext i
    dsimp only
    field_simp [ne_of_gt (H.sqrt_sampling_pos i)]
  right_inv f := by
    funext i
    dsimp only
    field_simp [ne_of_gt (H.sqrt_sampling_pos i)]
  map_add' g h := by funext i; exact add_div _ _ _
  map_smul' c g := by
    funext i
    change (c*g i)/Real.sqrt (H.sampling i)=c*(g i/Real.sqrt (H.sampling i))
    ring

def scaledEigenbasis (H : HoldingFamily ι) : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) :=
  H.scaledGeneratorMatrix_isHermitian.eigenvectorBasis

def generatorEigenvalues (H : HoldingFamily ι) : ι → ℝ :=
  H.scaledGeneratorMatrix_isHermitian.eigenvalues

def fullGeneratorEigenbasis (H : HoldingFamily ι) : Module.Basis ι ℝ (ι → ℝ) :=
  H.scaledEigenbasis.toBasis.map ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans H.unscaleEquiv)

theorem fullGeneratorEigenbasis_apply (H : HoldingFamily ι) (n i : ι) :
    H.fullGeneratorEigenbasis n i=H.scaledEigenbasis n i/Real.sqrt (H.sampling i) := rfl

theorem fullGeneratorEigenbasis_eigen (H : HoldingFamily ι) (n : ι) :
    H.generator (H.fullGeneratorEigenbasis n)=(fun i ↦ H.generatorEigenvalues n*H.fullGeneratorEigenbasis n i) := by
  have he := H.scaledGeneratorMatrix_isHermitian.mulVec_eigenvectorBasis n
  funext i
  have hi := congrFun he i
  rw [H.scaledGeneratorMatrix_apply] at hi
  change Real.sqrt (H.sampling i)*H.generator (H.fullGeneratorEigenbasis n) i =
    H.generatorEigenvalues n*H.scaledEigenbasis n i at hi
  calc
    _ = (Real.sqrt (H.sampling i)*H.generator (H.fullGeneratorEigenbasis n) i)/Real.sqrt (H.sampling i) := by
      field_simp [ne_of_gt (H.sqrt_sampling_pos i)]
    _ = (H.generatorEigenvalues n*H.scaledEigenbasis n i)/Real.sqrt (H.sampling i) := by rw [hi]
    _ = _ := by rw [H.fullGeneratorEigenbasis_apply]; ring

theorem fullGeneratorEigenbasis_orthonormal (H : HoldingFamily ι) (m n : ι) :
    FiniteKernel.weightedInner H.sampling (H.fullGeneratorEigenbasis m) (H.fullGeneratorEigenbasis n) =
      if m=n then 1 else 0 := by
  rw [← H.scaledEigenbasis.inner_eq_ite m n]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Pi.star_apply,star_trivial]
  unfold FiniteKernel.weightedInner ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [H.fullGeneratorEigenbasis_apply,H.fullGeneratorEigenbasis_apply]
  calc
    _ = (Real.sqrt (H.sampling i))^2*
        (H.scaledEigenbasis m i/Real.sqrt (H.sampling i)*(H.scaledEigenbasis n i/Real.sqrt (H.sampling i))) := by
      rw [Real.sq_sqrt (H.sampling.nonneg i)]
    _ = H.scaledEigenbasis m i*H.scaledEigenbasis n i := by
      field_simp [ne_of_gt (H.sqrt_sampling_pos i)]
    _ = _ := mul_comm _ _

theorem fullGeneratorEigenbasis_unit (H : HoldingFamily ι) (n : ι) :
    H.sampling.squareNorm (H.fullGeneratorEigenbasis n)=1 := by
  have h := H.fullGeneratorEigenbasis_orthonormal n n
  have hid : FiniteKernel.weightedInner H.sampling (H.fullGeneratorEigenbasis n) (H.fullGeneratorEigenbasis n) =
      H.sampling.squareNorm (H.fullGeneratorEigenbasis n) := by
    simp only [FiniteKernel.weightedInner,ProbabilityVector.mean,ProbabilityVector.squareNorm,pow_two]
  rw [hid,ite_eq_left rfl] at h
  exact h

theorem fullGeneratorEigenbasis_centered_of_ne_zero (H : HoldingFamily ι) (n : ι)
    (hn : H.generatorEigenvalues n ≠ 0) : H.sampling.mean (H.fullGeneratorEigenbasis n)=0 := by
  have hm := H.generator_sampling_mean (H.fullGeneratorEigenbasis n)
  rw [H.fullGeneratorEigenbasis_eigen,ProbabilityVector.mean_const_mul] at hm
  exact (mul_eq_zero.mp hm).resolve_left hn

theorem generatorEigenvalues_bounds_of_ne_zero (H : HoldingFamily ι) (n : ι)
    (hn : H.generatorEigenvalues n ≠ 0) : 1/2 ≤ H.generatorEigenvalues n ∧ H.generatorEigenvalues n ≤ H.maxRatio :=
  H.generator_eigenvalue_bounds (H.fullGeneratorEigenbasis n) (H.generatorEigenvalues n)
    (H.fullGeneratorEigenbasis_centered_of_ne_zero n hn) (H.fullGeneratorEigenbasis_unit n)
    (H.fullGeneratorEigenbasis_eigen n)

theorem generatorEigenvalues_nonneg (H : HoldingFamily ι) (n : ι) : 0 ≤ H.generatorEigenvalues n := by
  by_cases hn : H.generatorEigenvalues n=0
  · rw [hn]
  · have h := (H.generatorEigenvalues_bounds_of_ne_zero n hn).1
    linarith

theorem generator_zero_implies_constant (H : HoldingFamily ι) (f : ι → ℝ)
    (hf : H.generator f=0) : f=(fun _ ↦ H.refresh.mean f) := by
  have hvar : H.refresh.variance f=0 := by
    rw [← H.generator_quadratic,hf]
    simp only [FiniteKernel.weightedInner,ProbabilityVector.mean,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  unfold ProbabilityVector.variance at hvar
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_hi : i ∈ Finset.univ) ↦
    mul_nonneg (H.refresh.nonneg i) (sq_nonneg (H.refresh.center f i)))).mp hvar
  funext i
  have hs : (H.refresh.center f i)^2=0 :=
    (mul_eq_zero.mp (hterm i (Finset.mem_univ i))).resolve_left (ne_of_gt (H.refresh_pos i))
  have hc := sq_eq_zero_iff.mp hs
  exact sub_eq_zero.mp hc

theorem fullGeneratorEigenbasis_kernel_iterate (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (n : ι) (k : ℕ) :
    ((H.kernel τ hτ).act)^[k] (H.fullGeneratorEigenbasis n) =
      (fun i ↦ (Upper.eigenMultiplier τ (H.generatorEigenvalues n))^k*H.fullGeneratorEigenbasis n i) :=
  H.kernel_iterate_eigen_of_generator hτ (H.fullGeneratorEigenbasis n) (H.generatorEigenvalues_nonneg n)
    (H.fullGeneratorEigenbasis_eigen n) k

end
end Tournament.HoldingFamily
