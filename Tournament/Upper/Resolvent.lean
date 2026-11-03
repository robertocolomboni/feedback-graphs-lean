module

public import Tournament.Upper.Generator
public import Tournament.Upper.OccupationPotentials

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace FiniteKernel

variable {ι : Type*} [Fintype ι]

def actMap (P : FiniteKernel ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := P.act
  map_add' f g := by
    funext i
    simp only [act,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext i
    change (∑ j, P i j*(c*f j))=c*(∑ j, P i j*f j)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)

theorem act_const_mul (P : FiniteKernel ι) (c : ℝ) (f : ι → ℝ) :
    P.act (fun i ↦ c*f i)=(fun i ↦ c*P.act f i) := by
  change P.actMap (c • f)=c • P.actMap f
  exact map_smul P.actMap c f

theorem act_const (P : FiniteKernel ι) (c : ℝ) : P.act (fun _ ↦ c)=(fun _ ↦ c) := by
  funext i
  change (∑ j, P i j*c)=c
  rw [← Finset.sum_mul,P.row_sum,one_mul]

end FiniteKernel

namespace Upper

def eigenMultiplier (τ α : ℝ) : ℝ := (2+τ*α)/(2*(1+τ*α))

end Upper

namespace HoldingFamily

variable {ι : Type*} [Fintype ι]

def onePlusGeneratorMap (H : HoldingFamily ι) (τ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id+τ • H.generatorMap

def generatorResolvent (H : HoldingFamily ι) (τ : ℝ) (hτ : 0 < τ) (f : ι → ℝ) (i : ι) : ℝ :=
  2*(H.kernel τ hτ).act f i-f i

theorem destination_entry_explicit (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.destination τ hτ i=H.refresh i/((1+τ*H.ratio i)*H.destinationNormalizer τ) := by
  change (H.sampling i*H.refreshRate τ i)/H.meanRefreshRate τ = _
  calc
    _ = H.sampling i*(H.refreshRate τ i/H.meanRefreshRate τ) := by ring
    _ = _ := by
      rw [H.refreshRate_over_mean hτ i,← H.weighted_ratio i]
      ring

theorem generatorResolvent_formula (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (f : ι → ℝ) (i : ι) :
    H.generatorResolvent τ hτ f i =
      (f i+τ*H.ratio i*(H.destination τ hτ).mean f)/(1+τ*H.ratio i) := by
  have hden : 1+τ*H.ratio i ≠ 0 := ne_of_gt (by have := H.ratio_pos i; positivity)
  unfold generatorResolvent
  rw [H.kernel_act hτ]
  unfold refreshRate Upper.holdingFraction
  field_simp [hden]
  ring

theorem refresh_mean_resolvent (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (f : ι → ℝ) :
    H.refresh.mean (H.generatorResolvent τ hτ f)=(H.destination τ hτ).mean f := by
  let z := H.destinationNormalizer τ
  let d := (H.destination τ hτ).mean f
  have hz : z ≠ 0 := ne_of_gt (H.destinationNormalizer_pos (le_of_lt hτ))
  have hterm : ∀ i, H.refresh i*H.generatorResolvent τ hτ f i =
      z*(H.destination τ hτ i*f i)+(H.refresh i-z*H.destination τ hτ i)*d := by
    intro i
    have hden : 1+τ*H.ratio i ≠ 0 := ne_of_gt (by have := H.ratio_pos i; positivity)
    rw [H.generatorResolvent_formula,H.destination_entry_explicit]
    change H.refresh i*((f i+τ*H.ratio i*d)/(1+τ*H.ratio i)) =
      z*(H.refresh i/((1+τ*H.ratio i)*z)*f i)+(H.refresh i-z*(H.refresh i/((1+τ*H.ratio i)*z)))*d
    field_simp [hden,hz]
    ring
  change (∑ i, H.refresh i*H.generatorResolvent τ hτ f i)=d
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,Finset.sum_sub_distrib,
    ← Finset.mul_sum,H.refresh.sum_eq_one,(H.destination τ hτ).sum_eq_one,mul_one]
  change z*d+(1-z)*d=d
  ring

theorem generator_resolvent_identity (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (f : ι → ℝ) :
    H.onePlusGeneratorMap τ (H.generatorResolvent τ hτ f)=f := by
  funext i
  change H.generatorResolvent τ hτ f i+τ*H.generator (H.generatorResolvent τ hτ f) i=f i
  simp only [generator,H.refresh_mean_resolvent hτ,H.generatorResolvent_formula hτ]
  have hden : 1+τ*H.ratio i ≠ 0 := ne_of_gt (by have := H.ratio_pos i; positivity)
  field_simp [hden]
  ring

theorem onePlusGenerator_injective (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    Function.Injective (H.onePlusGeneratorMap τ) := by
  apply LinearMap.injective_iff_surjective.mpr
  intro f
  exact ⟨H.generatorResolvent τ hτ f,H.generator_resolvent_identity hτ f⟩

theorem kernel_eigen_of_generator (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (f : ι → ℝ) {α : ℝ} (hα : 0 ≤ α) (heigen : H.generator f=(fun i ↦ α*f i)) :
    (H.kernel τ hτ).act f=(fun i ↦ Upper.eigenMultiplier τ α*f i) := by
  let c := 1+τ*α
  have hc : 0 < c := by dsimp only [c]; positivity
  have hscaled : H.onePlusGeneratorMap τ ((1/c) • f)=f := by
    rw [map_smul]
    funext i
    change (1/c)*(f i+τ*H.generator f i)=f i
    rw [congrFun heigen i]
    dsimp only [c]
    field_simp [ne_of_gt hc]
  have hR := H.onePlusGenerator_injective hτ ((H.generator_resolvent_identity hτ f).trans hscaled.symm)
  funext i
  have hi := congrFun hR i
  change 2*(H.kernel τ hτ).act f i-f i=(1/c)*f i at hi
  have hp : (H.kernel τ hτ).act f i=(f i+(1/c)*f i)/2 := by linarith
  rw [hp]
  unfold Upper.eigenMultiplier
  dsimp only [c]
  field_simp [ne_of_gt hc]
  ring

theorem kernel_iterate_eigen_of_generator (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (f : ι → ℝ) {α : ℝ} (hα : 0 ≤ α) (heigen : H.generator f=(fun i ↦ α*f i)) (k : ℕ) :
    ((H.kernel τ hτ).act)^[k] f=(fun i ↦ (Upper.eigenMultiplier τ α)^k*f i) := by
  induction k with
  | zero => simp only [Function.iterate_zero,Function.id_def,pow_zero,one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,FiniteKernel.act_const_mul,
      H.kernel_eigen_of_generator hτ f hα heigen]
    funext i
    simp only [pow_succ]
    ring

end HoldingFamily

namespace Upper

theorem eigenMultiplier_bounds {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    1/2 ≤ eigenMultiplier τ α ∧ eigenMultiplier τ α ≤ 1 := by
  have hz : 0 ≤ τ*α := mul_nonneg hτ hα
  have hd : 0 < 2*(1+τ*α) := by positivity
  unfold eigenMultiplier
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

theorem spectralCorrelation_bounds {τ α : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hα : 0 ≤ α) :
    0 ≤ spectralCorrelation τ α ∧ spectralCorrelation τ α < 1 := by
  have hν := eigenMultiplier_bounds (le_of_lt hτ) hα
  change 0 ≤ (1-τ)*eigenMultiplier τ α ∧ (1-τ)*eigenMultiplier τ α < 1
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hτ1) (by linarith)
  · have hm := mul_le_mul_of_nonneg_left hν.2 (sub_nonneg.mpr hτ1)
    linarith

theorem energyWeight_eq_inv_eigenMultiplier_sub_one {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    energyWeight τ α=1/eigenMultiplier τ α-1 := by
  have hz : 0 ≤ τ*α := mul_nonneg hτ hα
  have hd : 1+τ*α ≠ 0 := ne_of_gt (by positivity)
  have hn : 2+τ*α ≠ 0 := ne_of_gt (by positivity)
  unfold energyWeight eigenMultiplier
  field_simp [hd,hn]
  ring

theorem one_sub_eigenMultiplier_eq {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    1-eigenMultiplier τ α=energyWeight τ α*eigenMultiplier τ α := by
  have hz : 0 ≤ τ*α := mul_nonneg hτ hα
  have hd : 1+τ*α ≠ 0 := ne_of_gt (by positivity)
  have hn : 2+τ*α ≠ 0 := ne_of_gt (by positivity)
  unfold energyWeight eigenMultiplier
  field_simp [hd,hn]
  ring

end Upper
end
end Tournament
