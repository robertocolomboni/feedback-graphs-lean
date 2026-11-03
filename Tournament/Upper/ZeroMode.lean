module

public import Tournament.Upper.SpectralRescaling
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Option

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem exists_zero_eigenIndex (H : HoldingFamily ι) : ∃ n, H.generatorEigenvalues n=0 := by
  by_contra h
  have hn : ∀ n, H.generatorEigenvalues n ≠ 0 := by
    intro n hz
    exact h ⟨n,hz⟩
  have hs := H.fullGeneratorEigenbasis.sum_repr (fun _ ↦ (1:ℝ))
  have hpoint : (fun i ↦ ∑ n, H.fullGeneratorEigenbasis.repr (fun _ ↦ (1:ℝ)) n*H.fullGeneratorEigenbasis n i) =
      (fun _ ↦ (1:ℝ)) := by
    funext i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun hs i
  have hm := congrArg H.sampling.mean hpoint
  rw [ProbabilityVector.mean_sum,ProbabilityVector.mean_const] at hm
  have hzero : (∑ n, H.sampling.mean (fun i ↦
      H.fullGeneratorEigenbasis.repr (fun _ ↦ (1:ℝ)) n*H.fullGeneratorEigenbasis n i)) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    rw [ProbabilityVector.mean_const_mul,H.fullGeneratorEigenbasis_centered_of_ne_zero n (hn n),mul_zero]
  rw [hzero] at hm
  norm_num at hm

theorem zero_eigenbasis_constant (H : HoldingFamily ι) (n : ι) (hn : H.generatorEigenvalues n=0) :
    H.fullGeneratorEigenbasis n=(fun _ ↦ H.refresh.mean (H.fullGeneratorEigenbasis n)) := by
  apply H.generator_zero_implies_constant
  rw [H.fullGeneratorEigenbasis_eigen,hn]
  funext i
  exact zero_mul _

theorem zero_eigenbasis_mean_sq (H : HoldingFamily ι) (n : ι) (hn : H.generatorEigenvalues n=0) :
    (H.refresh.mean (H.fullGeneratorEigenbasis n))^2=1 := by
  have hu := H.fullGeneratorEigenbasis_unit n
  have he := H.zero_eigenbasis_constant n hn
  have hfun : (fun i ↦ (H.fullGeneratorEigenbasis n i)^2) =
      (fun _ ↦ (H.refresh.mean (H.fullGeneratorEigenbasis n))^2) := by
    funext i
    rw [congrFun he i]
  change H.sampling.mean (fun i ↦ (H.fullGeneratorEigenbasis n i)^2)=1 at hu
  rw [hfun,ProbabilityVector.mean_const] at hu
  exact hu

theorem zero_eigenbasis_mean_ne_zero (H : HoldingFamily ι) (n : ι) (hn : H.generatorEigenvalues n=0) :
    H.refresh.mean (H.fullGeneratorEigenbasis n) ≠ 0 := by
  have hs := H.zero_eigenbasis_mean_sq n hn
  intro hz
  rw [hz] at hs
  norm_num at hs

theorem zero_eigenIndex_unique (H : HoldingFamily ι) (m n : ι)
    (hm : H.generatorEigenvalues m=0) (hn : H.generatorEigenvalues n=0) : m=n := by
  by_contra hmn
  have he_m := H.zero_eigenbasis_constant m hm
  have he_n := H.zero_eigenbasis_constant n hn
  have horth := H.fullGeneratorEigenbasis_orthonormal m n
  have hfun : (fun i ↦ H.fullGeneratorEigenbasis m i*H.fullGeneratorEigenbasis n i) =
      (fun _ ↦ H.refresh.mean (H.fullGeneratorEigenbasis m)*H.refresh.mean (H.fullGeneratorEigenbasis n)) := by
    funext i
    rw [congrFun he_m i,congrFun he_n i]
  unfold FiniteKernel.weightedInner at horth
  rw [hfun,ProbabilityVector.mean_const,ite_eq_right hmn] at horth
  exact mul_ne_zero (H.zero_eigenbasis_mean_ne_zero m hm) (H.zero_eigenbasis_mean_ne_zero n hn) horth

def zeroEigenIndex (H : HoldingFamily ι) : ι := Classical.choose H.exists_zero_eigenIndex

theorem eigenvalue_zeroEigenIndex (H : HoldingFamily ι) : H.generatorEigenvalues H.zeroEigenIndex=0 :=
  Classical.choose_spec H.exists_zero_eigenIndex

theorem eigenvalue_ne_zero_iff (H : HoldingFamily ι) (n : ι) :
    H.generatorEigenvalues n ≠ 0 ↔ n ≠ H.zeroEigenIndex := by
  constructor
  · intro hn heq
    subst n
    exact hn H.eigenvalue_zeroEigenIndex
  · intro hn heq
    exact hn (H.zero_eigenIndex_unique n H.zeroEigenIndex heq H.eigenvalue_zeroEigenIndex)

abbrev CenteredIndex (H : HoldingFamily ι) := {n : ι // n ≠ H.zeroEigenIndex}

instance centeredIndexFintype (H : HoldingFamily ι) : Fintype H.CenteredIndex :=
  inferInstanceAs (Fintype {n : ι // n ≠ H.zeroEigenIndex})

theorem centeredIndex_card (H : HoldingFamily ι) :
    Fintype.card H.CenteredIndex=Fintype.card ι-1 := by
  have hc := Fintype.card_congr (Equiv.optionSubtypeNe H.zeroEigenIndex)
  rw [Fintype.card_option] at hc
  change Fintype.card {n : ι // n ≠ H.zeroEigenIndex}=Fintype.card ι-1
  omega

def eigenvector (H : HoldingFamily ι) (n : H.CenteredIndex) : ι → ℝ := H.fullGeneratorEigenbasis n.val

def eigenvalue (H : HoldingFamily ι) (n : H.CenteredIndex) : ℝ := H.generatorEigenvalues n.val

theorem eigenvector_centered (H : HoldingFamily ι) (n : H.CenteredIndex) : H.sampling.mean (H.eigenvector n)=0 :=
  H.fullGeneratorEigenbasis_centered_of_ne_zero n.val ((H.eigenvalue_ne_zero_iff n.val).mpr n.property)

theorem eigenvalue_bounds (H : HoldingFamily ι) (n : H.CenteredIndex) :
    1/2 ≤ H.eigenvalue n ∧ H.eigenvalue n ≤ H.maxRatio :=
  H.generatorEigenvalues_bounds_of_ne_zero n.val ((H.eigenvalue_ne_zero_iff n.val).mpr n.property)

theorem eigenvector_generator (H : HoldingFamily ι) (n : H.CenteredIndex) :
    H.generator (H.eigenvector n)=(fun i ↦ H.eigenvalue n*H.eigenvector n i) :=
  H.fullGeneratorEigenbasis_eigen n.val

theorem eigenvectors_orthonormal (H : HoldingFamily ι) (m n : H.CenteredIndex) :
    FiniteKernel.weightedInner H.sampling (H.eigenvector m) (H.eigenvector n)=if m=n then 1 else 0 := by
  have h := H.fullGeneratorEigenbasis_orthonormal m.val n.val
  have heq : m.val=n.val ↔ m=n := ⟨fun he ↦ Subtype.ext he,fun he ↦ congrArg Subtype.val he⟩
  simpa only [eigenvector,heq] using h

theorem eigenvector_kernel (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (n : H.CenteredIndex) :
    (H.kernel τ hτ).act (H.eigenvector n)=(fun i ↦ Upper.eigenMultiplier τ (H.eigenvalue n)*H.eigenvector n i) :=
  H.kernel_eigen_of_generator hτ (H.eigenvector n) (by have := (H.eigenvalue_bounds n).1; linarith)
    (H.eigenvector_generator n)

end
end Tournament.HoldingFamily
