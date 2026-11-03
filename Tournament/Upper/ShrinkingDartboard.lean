module

public import Tournament.Upper.ExponentialWeights
public import Tournament.Probability.FiniteKernel
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open scoped Classical BigOperators

noncomputable section

theorem exp_neg_quadratic (z : ℝ) (hz : 0≤z) : Real.exp (-z)≤1-z+z^2/2 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 1-y+y^2/2-Real.exp (-y)) (-1+x+Real.exp (-x)) x := by
    convert (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
        ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg) using 1 <;> norm_num
    all_goals rfl
  have hmono := monotone_of_hasDerivAt_nonneg hd (fun x ↦ by
    change 0≤-1+x+Real.exp (-x)
    have h := Real.add_one_le_exp (-x)
    linarith)
  have h := hmono hz
  simp only [sub_zero,zero_pow (by decide : 2≠0),zero_div,add_zero,neg_zero,Real.exp_zero,sub_self] at h
  linarith

variable {ι : Type*} [Fintype ι]

def keep (η : ℝ) (g : ι → ℝ) (i : ι) : ℝ := Real.exp (-η*g i)

omit [Fintype ι] in
theorem keep_pos (η : ℝ) (g : ι → ℝ) (i : ι) : 0<keep η g i := Real.exp_pos _

omit [Fintype ι] in
theorem keep_le_one (η : ℝ) (hη : 0≤η) (g : ι → ℝ) (hg : ∀ i, 0≤g i) (i : ι) : keep η g i≤1 := by
  apply Real.exp_le_one_iff.mpr
  simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hη (hg i))

def kernel (π : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ) (hg : ∀ i, 0≤g i) : FiniteKernel ι where
  entry i j := (if i=j then keep η g i else 0)+(1-keep η g i)*Model.exponentialUpdate π η g j
  nonneg i j := add_nonneg (by split_ifs; exact (keep_pos η g i).le; exact le_rfl)
    (mul_nonneg (sub_nonneg.mpr (keep_le_one η hη g hg i)) ((Model.exponentialUpdate π η g).nonneg j))
  row_sum i := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,(Model.exponentialUpdate π η g).sum_eq_one]
    simp

theorem kernel_marginal (π : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ)
    (hg : ∀ i, 0≤g i) (j : ι) :
    (∑ i, π i*kernel π η hη g hg i j)=Model.exponentialUpdate π η g j := by
  let Z := π.mean (fun i ↦ keep η g i)
  have hZ : Z≠0 := (Model.exponentialNormalizer_pos π η g).ne'
  have hupdate : Model.exponentialUpdate π η g j*Z=π j*keep η g j := by
    exact div_mul_cancel₀ _ hZ
  have hsum : (∑ i, π i*(1-keep η g i))=1-Z := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [mul_one,π.sum_eq_one]
    rfl
  calc
    _ = π j*keep η g j+(∑ i, π i*(1-keep η g i))*Model.exponentialUpdate π η g j := by
      simp only [kernel,mul_add,Finset.sum_add_distrib,Finset.sum_mul,mul_ite,mul_zero]
      congr 1
      · simp [eq_comm]
      · apply Finset.sum_congr rfl
        intro i _
        ring
    _ = π j*keep η g j+(1-Z)*Model.exponentialUpdate π η g j := by rw [hsum]
    _ = _ := by nlinarith [hupdate]

theorem kernel_switch_le (π : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ)
    (hg : ∀ i, 0≤g i) (i : ι) :
    ((kernel π η hη g hg).row i).mean (fun j ↦ if j=i then 0 else 1)≤η*g i := by
  rw [FiniteKernel.row_switch_probability]
  have hresample : 0≤(1-keep η g i)*Model.exponentialUpdate π η g i :=
    mul_nonneg (sub_nonneg.mpr (keep_le_one η hη g hg i)) ((Model.exponentialUpdate π η g).nonneg i)
  have hExp := Real.add_one_le_exp (-η*g i)
  change 1-((if i=i then keep η g i else 0)+(1-keep η g i)*Model.exponentialUpdate π η g i)≤_
  simp only [ite_true]
  unfold keep at hresample ⊢
  linarith

theorem nonnegative_normalizer_le (π : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ)
    (hg : ∀ i, 0≤g i) :
    ExponentialWeights.normalizer π η g≤1-η*π.mean g+(η^2/2)*π.squareNorm g := by
  calc
    _ ≤ π.mean (fun i ↦ 1-η*g i+(η*g i)^2/2) := by
      apply π.mean_mono
      intro i
      simpa only [neg_mul] using exp_neg_quadratic (η*g i) (mul_nonneg hη (hg i))
    _ = _ := by
      have heq : (fun i ↦ 1-η*g i+(η*g i)^2/2)=(fun i ↦ (1-η*g i)+(η^2/2)*(g i)^2) := by
        funext i
        ring
      rw [heq,ProbabilityVector.mean_add,ProbabilityVector.mean_sub,ProbabilityVector.mean_const,
        ProbabilityVector.mean_const_mul,ProbabilityVector.mean_const_mul]
      rfl

theorem nonnegative_logNormalizer_le (π : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ)
    (hg : ∀ i, 0≤g i) :
    Real.log (ExponentialWeights.normalizer π η g)≤-η*π.mean g+(η^2/2)*π.squareNorm g := by
  have hlog := Real.log_le_sub_one_of_pos (Model.exponentialNormalizer_pos π η g)
  have hnorm := nonnegative_normalizer_le π η hη g hg
  unfold ExponentialWeights.normalizer at hnorm ⊢
  linarith

theorem nonnegative_second_order_from_initial (π₀ : ProbabilityVector ι) (hπ : ∀ i, 0<π₀ i)
    (η : ℝ) (hη : 0<η) (g : ℕ → ι → ℝ) (n : ℕ)
    (hg : ∀ t∈Finset.range n, ∀ i, 0≤g t i) (i : ι) :
    (∑ t∈Finset.range n, ((ExponentialWeights.trajectory π₀ η g t).mean (g t)-g t i))≤
      -Real.log (π₀ i)/η+(η/2)*(∑ t∈Finset.range n, (ExponentialWeights.trajectory π₀ η g t).squareNorm (g t)) := by
  have hlog := Real.log_nonpos (le_of_lt (ExponentialWeights.trajectory_pos π₀ hπ η g n i))
    ((ExponentialWeights.trajectory π₀ η g n).weight_le_one i)
  rw [ExponentialWeights.logTrajectory π₀ hπ η g n i] at hlog
  have hnorm : (∑ t∈Finset.range n, Real.log (ExponentialWeights.normalizer (ExponentialWeights.trajectory π₀ η g t) η (g t)))≤
      -η*(∑ t∈Finset.range n, (ExponentialWeights.trajectory π₀ η g t).mean (g t))+
        (η^2/2)*(∑ t∈Finset.range n, (ExponentialWeights.trajectory π₀ η g t).squareNorm (g t)) := by
    calc
      _ ≤ ∑ t∈Finset.range n, (-η*(ExponentialWeights.trajectory π₀ η g t).mean (g t)+
          (η^2/2)*(ExponentialWeights.trajectory π₀ η g t).squareNorm (g t)) :=
        Finset.sum_le_sum (fun t ht ↦ nonnegative_logNormalizer_le _ η hη.le (g t) (hg t ht))
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  calc
    _ ≤ (-Real.log (π₀ i)+(η^2/2)*(∑ t∈Finset.range n,
        (ExponentialWeights.trajectory π₀ η g t).squareNorm (g t)))/η := by
      apply (le_div_iff₀ hη).mpr
      nlinarith
    _ = _ := by field_simp

theorem nonnegative_second_order [Nonempty ι] (η : ℝ) (hη : 0<η) (g : ℕ → ι → ℝ) (n : ℕ)
    (hg : ∀ t∈Finset.range n, ∀ i, 0≤g t i) (i : ι) :
    (∑ t∈Finset.range n, ((ExponentialWeights.trajectory ExponentialWeights.uniform η g t).mean (g t)-g t i))≤
      Real.log (Fintype.card ι:ℝ)/η+(η/2)*(∑ t∈Finset.range n,
        (ExponentialWeights.trajectory ExponentialWeights.uniform η g t).squareNorm (g t)) := by
  have h := nonnegative_second_order_from_initial ExponentialWeights.uniform ExponentialWeights.uniform_pos η hη g n hg i
  rwa [ExponentialWeights.uniform_log,neg_neg] at h

end
end Tournament.Upper.ShrinkingDartboard
