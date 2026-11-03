module

public import Tournament.Upper.HoldingFamily
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {ι : Type*} [Fintype ι]

theorem squareNorm_eq_variance_add_mean_sq (p : ProbabilityVector ι) (f : ι → ℝ) :
    p.squareNorm f=p.variance f+(p.mean f)^2 := by
  have h := p.sum_sq_sub_eq_variance_add f 0
  simpa only [sub_zero,squareNorm] using h

end ProbabilityVector

namespace HoldingFamily

variable {ι : Type*} [Fintype ι]

def generator (H : HoldingFamily ι) (f : ι → ℝ) (i : ι) : ℝ :=
  H.ratio i*(f i-H.refresh.mean f)

def generatorMatrix (H : HoldingFamily ι) (i j : ι) : ℝ :=
  H.ratio i*((if i=j then 1 else 0)-H.refresh j)

theorem generatorMatrix_apply (H : HoldingFamily ι) (f : ι → ℝ) (i : ι) :
    (∑ j, H.generatorMatrix i j*f j) = H.generator f i := by
  unfold generatorMatrix generator ProbabilityVector.mean
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  simp [mul_ite,mul_assoc,Finset.mul_sum]

theorem weighted_generatorMatrix (H : HoldingFamily ι) (i j : ι) :
    H.sampling i*H.generatorMatrix i j = (if i=j then H.refresh i else 0)-H.refresh i*H.refresh j := by
  unfold generatorMatrix
  calc
    _ = (H.sampling i*H.ratio i)*((if i=j then 1 else 0)-H.refresh j) := by ring
    _ = _ := by
      rw [H.weighted_ratio]
      split <;> ring

theorem weighted_generatorMatrix_symmetric (H : HoldingFamily ι) (i j : ι) :
    H.sampling i*H.generatorMatrix i j=H.sampling j*H.generatorMatrix j i := by
  rw [H.weighted_generatorMatrix,H.weighted_generatorMatrix]
  by_cases hij : i=j
  · subst j; rfl
  · rw [ite_eq_right hij,ite_eq_right (Ne.symm hij)]
    ring

theorem generator_const (H : HoldingFamily ι) (c : ℝ) : H.generator (fun _ ↦ c) = 0 := by
  funext i
  simp only [generator,ProbabilityVector.mean_const,sub_self,mul_zero,Pi.zero_apply]

theorem generator_add (H : HoldingFamily ι) (f g : ι → ℝ) :
    H.generator (fun i ↦ f i+g i) = (fun i ↦ H.generator f i+H.generator g i) := by
  funext i
  simp only [generator,ProbabilityVector.mean_add]
  ring

theorem generator_const_mul (H : HoldingFamily ι) (c : ℝ) (f : ι → ℝ) :
    H.generator (fun i ↦ c*f i) = (fun i ↦ c*H.generator f i) := by
  funext i
  simp only [generator,ProbabilityVector.mean_const_mul]
  ring

def generatorMap (H : HoldingFamily ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := H.generator
  map_add' := H.generator_add
  map_smul' c f := by
    change H.generator (fun i ↦ c*f i)=(fun i ↦ c*H.generator f i)
    exact H.generator_const_mul c f

theorem generator_sampling_mean (H : HoldingFamily ι) (f : ι → ℝ) : H.sampling.mean (H.generator f)=0 := by
  have hterm : ∀ i, H.sampling i*H.generator f i = H.refresh i*(f i-H.refresh.mean f) := by
    intro i
    unfold generator
    rw [← mul_assoc,H.weighted_ratio]
  unfold ProbabilityVector.mean
  simp_rw [hterm]
  change H.refresh.mean (H.refresh.center f)=0
  exact ProbabilityVector.mean_center H.refresh f

theorem inner_generator (H : HoldingFamily ι) (f g : ι → ℝ) :
    FiniteKernel.weightedInner H.sampling f (H.generator g) =
      H.refresh.mean (fun i ↦ f i*g i)-H.refresh.mean f*H.refresh.mean g := by
  unfold FiniteKernel.weightedInner ProbabilityVector.mean
  have hterm : ∀ i, H.sampling i*(f i*H.generator g i) =
      H.refresh i*(f i*g i)-(H.refresh i*f i)*H.refresh.mean g := by
    intro i
    unfold generator
    calc
      _ = (H.sampling i*H.ratio i)*(f i*(g i-H.refresh.mean g)) := by ring
      _ = _ := by rw [H.weighted_ratio]; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  rfl

theorem generator_symmetric (H : HoldingFamily ι) (f g : ι → ℝ) :
    FiniteKernel.weightedInner H.sampling f (H.generator g) =
      FiniteKernel.weightedInner H.sampling g (H.generator f) := by
  rw [H.inner_generator,H.inner_generator]
  have hfg : (fun i ↦ f i*g i)=(fun i ↦ g i*f i) := funext (fun _ ↦ mul_comm _ _)
  rw [hfg,mul_comm (H.refresh.mean f) (H.refresh.mean g)]

theorem generator_quadratic (H : HoldingFamily ι) (f : ι → ℝ) :
    FiniteKernel.weightedInner H.sampling f (H.generator f)=H.refresh.variance f := by
  rw [H.inner_generator]
  have hs := H.refresh.squareNorm_eq_variance_add_mean_sq f
  have hprod : H.refresh.mean (fun i ↦ f i*f i)=H.refresh.squareNorm f := by
    simp only [ProbabilityVector.mean,ProbabilityVector.squareNorm,pow_two]
  rw [hprod]
  nlinarith

theorem generator_Rayleigh_bounds (H : HoldingFamily ι) (f : ι → ℝ) (hf : H.sampling.mean f=0) :
    H.sampling.squareNorm f/2 ≤ H.refresh.variance f ∧
      H.refresh.variance f ≤ H.maxRatio*H.sampling.squareNorm f := by
  have hpvar : H.sampling.variance f=H.sampling.squareNorm f := by
    simp only [ProbabilityVector.variance,ProbabilityVector.center,hf,sub_zero,ProbabilityVector.squareNorm]
  have hlow := H.sampling.variance_le_mul_variance H.refresh f 2 (by norm_num)
    (fun i ↦ by have := H.refresh_ge_half i; linarith)
  rw [hpvar] at hlow
  constructor
  · linarith
  · calc
      _ ≤ ∑ i, H.refresh i*(f i-0)^2 := H.refresh.variance_le_sum_sq_sub f 0
      _ ≤ ∑ i, H.maxRatio*(H.sampling i*f i^2) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := mul_le_mul_of_nonneg_left (H.ratio_le_maxRatio i) (H.sampling.nonneg i)
        rw [H.weighted_ratio] at hi
        simpa only [sub_zero,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_right hi (sq_nonneg (f i))
      _ = _ := (Finset.mul_sum _ _ _).symm

theorem generator_eigenvalue_bounds (H : HoldingFamily ι) (f : ι → ℝ) (α : ℝ)
    (hf : H.sampling.mean f=0) (hunit : H.sampling.squareNorm f=1)
    (heigen : H.generator f=(fun i ↦ α*f i)) : 1/2 ≤ α ∧ α ≤ H.maxRatio := by
  have hquad := H.generator_quadratic f
  rw [heigen] at hquad
  have hinner : FiniteKernel.weightedInner H.sampling f (fun i ↦ α*f i) = α*H.sampling.squareNorm f := by
    unfold FiniteKernel.weightedInner ProbabilityVector.mean ProbabilityVector.squareNorm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [hinner,hunit,mul_one] at hquad
  have hb := H.generator_Rayleigh_bounds f hf
  rw [hunit,← hquad] at hb
  simpa only [mul_one] using hb

end HoldingFamily
end
end Tournament
