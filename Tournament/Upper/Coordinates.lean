module

public import Tournament.Upper.CenteredBasis
public import Tournament.Foundations.WeightedInner

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

def coordinate (H : HoldingFamily ι) (f : ι → ℝ) (n : H.CenteredIndex) : ℝ :=
  weightedInner H.sampling (H.eigenvector n) f

theorem basis_repr_inner (H : HoldingFamily ι) (f : ι → ℝ) (n : Option H.CenteredIndex) :
    H.constantCenteredBasis.repr f n=weightedInner H.sampling (H.constantCenteredBasis n) f := by
  have hs := H.constantCenteredBasis.sum_repr f
  have hpoint : (fun i ↦ ∑ m, H.constantCenteredBasis.repr f m*H.constantCenteredBasis m i)=f := by
    funext i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun hs i
  symm
  calc
    _ = weightedInner H.sampling (H.constantCenteredBasis n)
        (fun i ↦ ∑ m, H.constantCenteredBasis.repr f m*H.constantCenteredBasis m i) := by rw [hpoint]
    _ = ∑ m, H.constantCenteredBasis.repr f m*
        weightedInner H.sampling (H.constantCenteredBasis n) (H.constantCenteredBasis m) := by
      rw [weightedInner_sum_right]
      apply Finset.sum_congr rfl
      intro m _
      exact weightedInner_const_mul_right _ _ _ _
    _ = H.constantCenteredBasis.repr f n := by
      simp only [H.constantCenteredBasis_orthonormal,mul_ite,mul_one,mul_zero]
      rw [Finset.sum_eq_single n]
      · rw [ite_eq_left rfl]
      · intro m _ hmn
        rw [ite_eq_right (Ne.symm hmn)]
      · intro hn
        exact False.elim (hn (Finset.mem_univ n))

theorem basis_repr_none (H : HoldingFamily ι) (f : ι → ℝ) :
    H.constantCenteredBasis.repr f none=H.sampling.mean f := by
  rw [H.basis_repr_inner,H.constantCenteredBasis_none,weightedInner_const_left,one_mul]

theorem basis_repr_some (H : HoldingFamily ι) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.constantCenteredBasis.repr f (some n)=H.coordinate f n := by
  rw [H.basis_repr_inner,H.constantCenteredBasis_some]
  rfl

theorem vector_expansion (H : HoldingFamily ι) (f : ι → ℝ) :
    f=(fun i ↦ H.sampling.mean f+∑ n, H.coordinate f n*H.eigenvector n i) := by
  have hs := H.constantCenteredBasis.sum_repr f
  funext i
  calc
    f i = ∑ n : Option H.CenteredIndex, H.constantCenteredBasis.repr f n*H.constantCenteredBasis n i := by
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (congrFun hs i).symm
    _ = _ := by
      rw [Fintype.sum_option]
      simp only [H.basis_repr_none,H.basis_repr_some,H.constantCenteredBasis_none,H.constantCenteredBasis_some,mul_one]

theorem inner_coordinates (H : HoldingFamily ι) (f g : ι → ℝ) :
    weightedInner H.sampling f g=H.sampling.mean f*H.sampling.mean g+
      ∑ n, H.coordinate f n*H.coordinate g n := by
  calc
    _ = weightedInner H.sampling f (fun i ↦ H.sampling.mean g+∑ n, H.coordinate g n*H.eigenvector n i) := by
      rw [← H.vector_expansion g]
    _ = _ := by
      rw [weightedInner_add,weightedInner_const_right,weightedInner_sum_right]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      rw [weightedInner_const_mul_right,weightedInner_comm H.sampling f (H.eigenvector n)]
      change H.coordinate g n*H.coordinate f n=H.coordinate f n*H.coordinate g n
      ring

theorem variance_coordinates (H : HoldingFamily ι) (f : ι → ℝ) :
    H.sampling.variance f=∑ n, (H.coordinate f n)^2 := by
  have hi := H.inner_coordinates f f
  rw [weightedInner_self,H.sampling.squareNorm_eq_variance_add_mean_sq] at hi
  have hsq : (∑ n, H.coordinate f n*H.coordinate f n)=∑ n, (H.coordinate f n)^2 := by
    simp only [pow_two]
  rw [hsq] at hi
  nlinarith

theorem generator_coordinate (H : HoldingFamily ι) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (H.generator f) n=H.eigenvalue n*H.coordinate f n := by
  unfold coordinate
  rw [H.generator_symmetric,H.eigenvector_generator,weightedInner_const_mul_right,
    weightedInner_comm H.sampling f (H.eigenvector n)]

theorem refresh_variance_coordinates (H : HoldingFamily ι) (f : ι → ℝ) :
    H.refresh.variance f=∑ n, H.eigenvalue n*(H.coordinate f n)^2 := by
  rw [← H.generator_quadratic,H.inner_coordinates,H.generator_sampling_mean,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro n _
  rw [H.generator_coordinate]
  ring

theorem kernel_iterate_coordinate (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (k : ℕ) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (((H.kernel τ hτ).act)^[k] f) n=
      (Upper.eigenMultiplier τ (H.eigenvalue n))^k*H.coordinate f n := by
  unfold coordinate
  rw [FiniteKernel.weightedInner_iterate_selfadjoint _ _ (H.kernel_reversible hτ)]
  have he := H.kernel_iterate_eigen_of_generator hτ (H.eigenvector n)
    (by have := (H.eigenvalue_bounds n).1; linarith : 0 ≤ H.eigenvalue n) (H.eigenvector_generator n) k
  rw [he,weightedInner_const_mul_left]

theorem bounded_refresh_variance_le_quarter (H : HoldingFamily ι) (loss : ι → ℝ)
    (hloss : Upper.BoundedLoss loss) : H.refresh.variance loss ≤ 1/4 := by
  calc
    _ ≤ ∑ i, H.refresh i*(loss i-1/2)^2 := H.refresh.variance_le_sum_sq_sub loss (1/2)
    _ ≤ ∑ i, H.refresh i*(1/4) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (H.refresh.nonneg i)
      have hi := hloss i
      nlinarith [mul_nonneg hi.1 (sub_nonneg.mpr hi.2)]
    _ = 1/4 := H.refresh.mean_const (1/4)

theorem bounded_weighted_coordinates_le_quarter (H : HoldingFamily ι) (loss : ι → ℝ)
    (hloss : Upper.BoundedLoss loss) : ∑ n, H.eigenvalue n*(H.coordinate loss n)^2 ≤ 1/4 := by
  rw [← H.refresh_variance_coordinates]
  exact H.bounded_refresh_variance_le_quarter loss hloss

end
end Tournament.HoldingFamily
