module

public import Tournament.Upper.ZeroMode
public import Mathlib.LinearAlgebra.Basis.SMul

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def eigenNormalization (H : HoldingFamily ι) (n : ι) : ℝ :=
  if n=H.zeroEigenIndex then H.refresh.mean (H.fullGeneratorEigenbasis H.zeroEigenIndex) else 1

theorem eigenNormalization_ne_zero (H : HoldingFamily ι) (n : ι) : H.eigenNormalization n ≠ 0 := by
  unfold eigenNormalization
  split
  · exact H.zero_eigenbasis_mean_ne_zero H.zeroEigenIndex H.eigenvalue_zeroEigenIndex
  · exact one_ne_zero

def normalizedFullEigenbasis (H : HoldingFamily ι) : Module.Basis ι ℝ (ι → ℝ) :=
  H.fullGeneratorEigenbasis.isUnitSMul (fun n ↦ isUnit_iff_ne_zero.mpr (H.eigenNormalization_ne_zero n))

theorem normalizedFullEigenbasis_apply (H : HoldingFamily ι) (n : ι) :
    H.normalizedFullEigenbasis n=(fun i ↦ H.eigenNormalization n*H.fullGeneratorEigenbasis n i) := by
  unfold normalizedFullEigenbasis
  rw [Module.Basis.isUnitSMul_apply]
  rfl

def constantCenteredBasis (H : HoldingFamily ι) : Module.Basis (Option H.CenteredIndex) ℝ (ι → ℝ) :=
  H.normalizedFullEigenbasis.reindex (Equiv.optionSubtypeNe H.zeroEigenIndex).symm

theorem constantCenteredBasis_none (H : HoldingFamily ι) : H.constantCenteredBasis none=(fun _ ↦ (1:ℝ)) := by
  unfold constantCenteredBasis
  rw [Module.Basis.reindex_apply]
  change H.normalizedFullEigenbasis H.zeroEigenIndex=(fun _ ↦ (1:ℝ))
  rw [H.normalizedFullEigenbasis_apply]
  funext i
  rw [eigenNormalization,ite_eq_left rfl]
  have he := congrFun (H.zero_eigenbasis_constant H.zeroEigenIndex H.eigenvalue_zeroEigenIndex) i
  rw [he]
  have hs := H.zero_eigenbasis_mean_sq H.zeroEigenIndex H.eigenvalue_zeroEigenIndex
  nlinarith

theorem constantCenteredBasis_some (H : HoldingFamily ι) (n : H.CenteredIndex) :
    H.constantCenteredBasis (some n)=H.eigenvector n := by
  unfold constantCenteredBasis
  rw [Module.Basis.reindex_apply]
  change H.normalizedFullEigenbasis n.val=H.eigenvector n
  rw [H.normalizedFullEigenbasis_apply]
  funext i
  rw [eigenNormalization,ite_eq_right n.property,one_mul]
  rfl

theorem constantCenteredBasis_orthonormal (H : HoldingFamily ι) (m n : Option H.CenteredIndex) :
    FiniteKernel.weightedInner H.sampling (H.constantCenteredBasis m) (H.constantCenteredBasis n) =
      if m=n then 1 else 0 := by
  cases m with
  | none =>
    cases n with
    | none =>
      rw [H.constantCenteredBasis_none,ite_eq_left rfl]
      change H.sampling.mean (fun _ ↦ (1:ℝ)*1)=1
      simpa only [one_mul] using H.sampling.mean_const 1
    | some n =>
      rw [H.constantCenteredBasis_none,H.constantCenteredBasis_some,ite_eq_right (by simp)]
      change H.sampling.mean (fun i ↦ 1*H.eigenvector n i)=0
      simpa only [one_mul] using H.eigenvector_centered n
  | some m =>
    cases n with
    | none =>
      rw [H.constantCenteredBasis_some,H.constantCenteredBasis_none,ite_eq_right (by simp)]
      change H.sampling.mean (fun i ↦ H.eigenvector m i*1)=0
      simpa only [mul_one] using H.eigenvector_centered m
    | some n =>
      rw [H.constantCenteredBasis_some,H.constantCenteredBasis_some]
      simpa only [Option.some.injEq] using H.eigenvectors_orthonormal m n

theorem spectral_structure (H : HoldingFamily ι) :
    Fintype.card H.CenteredIndex=Fintype.card ι-1 ∧
    (H.constantCenteredBasis none=(fun _ ↦ (1:ℝ))) ∧
    (∀ n, H.constantCenteredBasis (some n)=H.eigenvector n) ∧
    (∀ n, H.sampling.mean (H.eigenvector n)=0 ∧
      H.generator (H.eigenvector n)=(fun i ↦ H.eigenvalue n*H.eigenvector n i) ∧
      1/2 ≤ H.eigenvalue n ∧ H.eigenvalue n ≤ H.maxRatio) ∧
    (∀ m n, FiniteKernel.weightedInner H.sampling (H.eigenvector m) (H.eigenvector n)=if m=n then 1 else 0) ∧
    (∀ τ (hτ : 0 < τ), (H.kernel τ hτ).act (fun _ ↦ (1:ℝ))=(fun _ ↦ (1:ℝ)) ∧
      (∀ n, (H.kernel τ hτ).act (H.eigenvector n)=(fun i ↦ Upper.eigenMultiplier τ (H.eigenvalue n)*H.eigenvector n i)) ∧
      (∀ f, H.onePlusGeneratorMap τ (H.generatorResolvent τ hτ f)=f)) := by
  refine ⟨H.centeredIndex_card,H.constantCenteredBasis_none,H.constantCenteredBasis_some,?_,
    H.eigenvectors_orthonormal,?_⟩
  · intro n
    exact ⟨H.eigenvector_centered n,H.eigenvector_generator n,(H.eigenvalue_bounds n).1,(H.eigenvalue_bounds n).2⟩
  · intro τ hτ
    exact ⟨FiniteKernel.act_const _ 1,H.eigenvector_kernel hτ,H.generator_resolvent_identity hτ⟩

end
end Tournament.HoldingFamily
