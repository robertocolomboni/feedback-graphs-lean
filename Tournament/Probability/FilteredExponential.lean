module

public import Tournament.Probability.FilteredMoments
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

namespace Tournament.FilteredMoments

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter OrderedMoments

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_exponential_integrable (V : Ω → ℝ) (hV : AEStronglyMeasurable V μ)
    (C : ℝ) (hVC : ∀ ω, V ω≤C) (θ : ℝ) (hθ : 0≤θ) :
    Integrable (fun ω ↦ Real.exp (θ*V ω)) μ := by
  apply (integrable_const (Real.exp (θ*C))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable (hV.const_mul θ))
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hVC ω) hθ)

theorem exponential_integral_of_moments (V : Ω → ℝ)
    (hV : AEStronglyMeasurable V μ) (hV0 : ∀ ω, 0≤V ω)
    (C : ℝ) (hVC : ∀ ω, V ω≤C) (B : ℝ) (hB : 0≤B)
    (hmoment : ∀ k, (∫ ω, V ω^(k+1) ∂μ)≤
      (Nat.factorial (k+1):ℝ)*B^k*(∫ ω, V ω ∂μ))
    (θ : ℝ) (hθ : 0≤θ) (hθB : θ*B<1) :
    (∫ ω, Real.exp (θ*V ω) ∂μ)≤1+θ*(∫ ω, V ω ∂μ)/(1-θ*B) := by
  let F := fun k ω ↦ (θ*V ω)^k/(Nat.factorial k:ℝ)
  let a := fun k ↦ ∫ ω, F k ω ∂μ
  let g := fun k ↦ if k=0 then (1:ℝ) else θ*(∫ ω, V ω ∂μ)*(θ*B)^(k-1)
  let bound := fun k (_ω : Ω) ↦ (θ*C)^k/(Nat.factorial k:ℝ)
  have hF : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    have h := ((hV.const_mul θ).pow k).const_mul ((Nat.factorial k:ℝ)⁻¹)
    simpa only [F,Pi.pow_apply,div_eq_mul_inv,mul_comm] using h
  have hb (k : ℕ) : ∀ᵐ ω ∂μ, ‖F k ω‖≤bound k ω := by
    apply Eventually.of_forall
    intro ω
    have hv : 0≤θ*V ω := mul_nonneg hθ (hV0 ω)
    dsimp only [F,bound]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (pow_nonneg hv k) (Nat.cast_nonneg _))]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hv (mul_le_mul_of_nonneg_left (hVC ω) hθ) k) (Nat.cast_nonneg _)
  have hs : ∀ᵐ ω ∂μ, Summable (fun k ↦ bound k ω) := Eventually.of_forall (fun _ ↦ by
    simpa only [bound] using (NormedSpace.expSeries_div_hasSum_exp (θ*C)).summable)
  have hi : Integrable (fun ω ↦ ∑' k, bound k ω) μ := by
    change Integrable (fun _ : Ω ↦ ∑' k, (θ*C)^k/(Nat.factorial k:ℝ)) μ
    exact integrable_const _
  have hlim : ∀ᵐ ω ∂μ, HasSum (fun k ↦ F k ω) (Real.exp (θ*V ω)) := Eventually.of_forall (fun ω ↦ by
    simpa only [F,← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (θ*V ω))
  have hexp : HasSum a (∫ ω, Real.exp (θ*V ω) ∂μ) :=
    hasSum_integral_of_dominated_convergence bound hF hb hs hi hlim
  have hnorm : ‖θ*B‖<1 := by rwa [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hθ hB)]
  have hgeom := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (θ*(∫ ω, V ω ∂μ))
  have htail : HasSum (fun k ↦ g (k+1)) (θ*(∫ ω, V ω ∂μ)/(1-θ*B)) := by
    simpa only [g,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
      div_eq_mul_inv] using hgeom
  have hmajorant : HasSum g (1+θ*(∫ ω, V ω ∂μ)/(1-θ*B)) := by
    have h := (hasSum_nat_add_iff 1).mp htail
    simpa only [Finset.sum_range_one,g,ite_eq_left rfl,ite_true,add_comm] using h
  have hle : ∀ k, a k≤g k := by
    intro k
    cases k with
    | zero => simp [a,F,g]
    | succ k =>
      have hfactorial : (Nat.factorial (k+1):ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (k+1)
      have heq : a (k+1)=(θ^(k+1)/(Nat.factorial (k+1):ℝ))*(∫ ω, V ω^(k+1) ∂μ) := by
        have hfun : F (k+1)=(fun ω ↦ (θ^(k+1)/(Nat.factorial (k+1):ℝ))*V ω^(k+1)) := by
          funext ω
          dsimp only [F]
          rw [mul_pow]
          ring
        dsimp only [a]
        rw [hfun,integral_const_mul]
      rw [heq]
      calc
        _ ≤ (θ^(k+1)/(Nat.factorial (k+1):ℝ))*
            ((Nat.factorial (k+1):ℝ)*B^k*(∫ ω, V ω ∂μ)) :=
          mul_le_mul_of_nonneg_left (hmoment k) (by positivity)
        _ = g (k+1) := by
          simp only [g,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,mul_pow,pow_succ]
          field_simp
  exact hasSum_le hle hexp hmajorant

theorem accumulated_exponential_integral (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b v : ℝ) (hB : 0<b+v)
    (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v)
    (θ : ℝ) (hθ : 0≤θ) (hθB : θ<1/(b+v)) :
    (∫ ω, Real.exp (θ*(∑ t ∈ Finset.range N, Y t ω)) ∂μ)≤
      1+θ*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)/(1-θ*(b+v)) := by
  have hV : Integrable (fun ω ↦ ∑ t ∈ Finset.range N, Y t ω) μ :=
    integrable_finsetSum _ (fun t ht ↦ variable_integrable μ history hglobal Y N hY hY0 b hbound t (Finset.mem_range.mp ht))
  exact exponential_integral_of_moments μ _ hV.aestronglyMeasurable
    (fun ω ↦ (total_bounds Y N hY0 b hbound ω).1) ((N:ℝ)*max b 0)
    (fun ω ↦ (total_bounds Y N hY0 b hbound ω).2) (b+v) hB.le
    (fun k ↦ accumulated_moment_integral μ history hmono hglobal Y N hY hY0 b v hB.le hbound hfuture k)
    θ hθ ((lt_div_iff₀ hB).mp hθB)

def finitePrefix (Y : ℕ → Ω → ℝ) (N t : ℕ) (ω : Ω) : ℝ := if t<N then Y t ω else 0

theorem accumulated_quantities (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (b v : ℝ) (hB : 0<b+v)
    (hbound : ∀ t, t<N → ∀ ω, 0≤Y t ω ∧ Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v)
    (θ : ℝ) (hθ : 0≤θ) (hθB : θ<1/(b+v)) :
    (∫ ω, Real.exp (θ*(∑ t ∈ Finset.range N, Y t ω)) ∂μ)≤
      1+θ*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)/(1-θ*(b+v)) := by
  let Z := finitePrefix Y N
  have hZ (t : ℕ) (ht : t<N) : AEStronglyMeasurable[history (t+1)] (Z t) μ := by
    have heq : Z t=Y t := funext (fun ω ↦ by simp only [Z,finitePrefix,ite_eq_left ht])
    rw [heq]
    exact hY t ht
  have hZ0 (t : ℕ) (ω : Ω) : 0≤Z t ω := by
    by_cases ht : t<N
    · simpa only [Z,finitePrefix,ite_eq_left ht] using (hbound t ht ω).1
    · simp only [Z,finitePrefix,ite_eq_right ht,le_refl]
  have hZbound (t : ℕ) (ht : t<N) (ω : Ω) : Z t ω≤b := by
    simpa only [Z,finitePrefix,ite_eq_left ht] using (hbound t ht ω).2
  have htail (t : ℕ) : (fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Z u ω else 0)=
      (fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0) := by
    funext ω
    apply Finset.sum_congr rfl
    intro u hu
    simp only [Z,finitePrefix,ite_eq_left (Finset.mem_range.mp hu)]
  have hZfuture (t : ℕ) (ht : t<N) : μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Z u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v := by
    rw [htail]
    exact hfuture t ht
  have htotal : (fun ω ↦ ∑ t ∈ Finset.range N, Z t ω)=(fun ω ↦ ∑ t ∈ Finset.range N, Y t ω) := by
    funext ω
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Z,finitePrefix,ite_eq_left (Finset.mem_range.mp ht)]
  have h := accumulated_exponential_integral μ history hmono hglobal Z N hZ hZ0 b v hB hZbound hZfuture θ hθ hθB
  have hsum (ω : Ω) : (∑ t ∈ Finset.range N, Z t ω)=(∑ t ∈ Finset.range N, Y t ω) := congrFun htotal ω
  simpa only [hsum] using h

end
end Tournament.FilteredMoments
