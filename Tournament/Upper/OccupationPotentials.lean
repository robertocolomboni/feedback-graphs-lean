module

public import Tournament.Probability.Occupation
public import Tournament.Upper.Scores

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

theorem kernel_act (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (g : ι → ℝ) (i : ι) :
    (H.kernel τ hτ).act g i =
      (1-H.refreshRate τ i)*g i + H.refreshRate τ i * (H.destination τ hτ).mean g := by
  change (∑ j, ((1-H.refreshRate τ i)*(if i=j then 1 else 0) +
    H.refreshRate τ i * H.destination τ hτ j)*g j) = _
  simp [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ProbabilityVector.mean]

theorem destination_mean_of_potential (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (f g : ι → ℝ) (m c : ℝ) (hf : H.sampling.mean f = m)
    (hg : ∀ i, H.refreshRate τ i * (g i-c) = f i-m) :
    (H.destination τ hτ).mean g = c := by
  have hzero : (H.destination τ hτ).mean (fun i ↦ g i-c) = 0 := by
    calc
      (H.destination τ hτ).mean (fun i ↦ g i-c) =
          H.sampling.mean (fun i ↦ H.refreshRate τ i * (g i-c)) / H.meanRefreshRate τ := by
        unfold ProbabilityVector.mean destination
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = H.sampling.mean (fun i ↦ f i-m) / H.meanRefreshRate τ := by
        congr 2
        funext i
        exact hg i
      _ = 0 := by rw [ProbabilityVector.mean_sub, ProbabilityVector.mean_const, hf, sub_self, zero_div]
  rw [ProbabilityVector.mean_sub, ProbabilityVector.mean_const] at hzero
  linarith

def ratioPotential (H : HoldingFamily ι) (τ : ℝ) (i : ι) : ℝ :=
  2*H.ratio i - 2/(τ*H.ratio i)

theorem ratioPotential_refresh (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.refreshRate τ i * (H.ratioPotential τ i - (2-2/τ)) = H.ratio i-1 := by
  have hratio := H.ratio_pos i
  have hden : 1+τ*H.ratio i ≠ 0 := ne_of_gt (by positivity)
  unfold ratioPotential refreshRate Upper.holdingFraction
  field_simp [ne_of_gt hτ, ne_of_gt hratio]
  ring

theorem ratioPotential_destination_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    (H.destination τ hτ).mean (H.ratioPotential τ) = 2-2/τ :=
  H.destination_mean_of_potential hτ H.ratio (H.ratioPotential τ) 1 (2-2/τ)
    H.mean_ratio (H.ratioPotential_refresh hτ)

theorem ratioPotential_poisson (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.ratioPotential τ i - (H.kernel τ hτ).act (H.ratioPotential τ) i = H.ratio i-1 := by
  rw [H.kernel_act hτ, H.ratioPotential_destination_mean hτ]
  have h := H.ratioPotential_refresh hτ i
  nlinarith

theorem ratioPotential_bounds (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    -4/τ ≤ H.ratioPotential τ i ∧ H.ratioPotential τ i ≤ 2*H.maxRatio := by
  have hr := H.ratio_pos i
  have hrhalf := H.ratio_ge_half i
  have hrmax := H.ratio_le_maxRatio i
  have hdiv : 2/(τ*H.ratio i) ≤ 4/τ := by
    apply (div_le_div_iff₀ (mul_pos hτ hr) hτ).mpr
    nlinarith
  have hdiv0 : 0 ≤ 2/(τ*H.ratio i) := by positivity
  unfold ratioPotential
  rw [neg_div]
  constructor <;> linarith

theorem expected_ratio_occupation_le (H : HoldingFamily ι) (μ : ProbabilityVector ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4)
    (hκτ : κ ≤ τ) (h : ℕ) (hhκ : (h:ℝ)*κ ≤ 1/8) (n : ℕ) (hn : n ≤ h) :
    (law (H.kernel τ (lt_of_lt_of_le hκ hκτ)) μ n).mean (occupation H.ratio n) ≤ 5/κ := by
  have hτ : 0 < τ := lt_of_lt_of_le hκ hκτ
  have hocc := occupation_mean_le (H.kernel τ hτ) μ H.ratio (H.ratioPotential τ)
    1 (-4/τ) (2*H.maxRatio) (H.ratioPotential_poisson hτ) (H.ratioPotential_bounds hτ) n
  have hn' : (n:ℝ) ≤ h := by exact_mod_cast hn
  have hmax : 2*H.maxRatio ≤ 1/(2*κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*κ)).mpr
    nlinarith
  have hrate : 4/τ ≤ 4/κ := by
    apply (div_le_div_iff₀ hτ hκ).mpr
    linarith
  have hh : (h:ℝ) ≤ 1/(8*κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 8*κ)).mpr
    nlinarith
  have hnumeric : 1/(8*κ)+1/(2*κ)+4/κ ≤ 5/κ := by
    apply (le_of_sub_nonneg ?_)
    have heq : 5/κ - (1/(8*κ)+1/(2*κ)+4/κ) = 3/(8*κ) := by
      field_simp
      ring
    rw [heq]
    positivity
  calc
    (law (H.kernel τ hτ) μ n).mean (occupation H.ratio n) ≤ (n:ℝ)+2*H.maxRatio+4/τ := by
      simpa only [mul_one, neg_div, sub_neg_eq_add] using hocc
    _ ≤ 1/(8*κ)+1/(2*κ)+4/κ := by linarith
    _ ≤ 5/κ := hnumeric

def refreshPotential (H : HoldingFamily ι) (τ : ℝ) (i : ι) : ℝ :=
  -H.meanRefreshRate τ / H.refreshRate τ i

theorem refreshPotential_refresh (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.refreshRate τ i * (H.refreshPotential τ i - (-1)) = H.refreshRate τ i-H.meanRefreshRate τ := by
  unfold refreshPotential
  field_simp [ne_of_gt (H.refreshRate_pos hτ i)]
  ring

theorem refreshPotential_destination_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) :
    (H.destination τ hτ).mean (H.refreshPotential τ) = -1 :=
  H.destination_mean_of_potential hτ (H.refreshRate τ) (H.refreshPotential τ)
    (H.meanRefreshRate τ) (-1) rfl (H.refreshPotential_refresh hτ)

theorem refreshPotential_poisson (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    H.refreshPotential τ i - (H.kernel τ hτ).act (H.refreshPotential τ) i =
      H.refreshRate τ i-H.meanRefreshRate τ := by
  rw [H.kernel_act hτ, H.refreshPotential_destination_mean hτ]
  have h := H.refreshPotential_refresh hτ i
  nlinarith

theorem refreshPotential_bounds (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (i : ι) :
    -3 ≤ H.refreshPotential τ i ∧ H.refreshPotential τ i ≤ 0 := by
  have ha := H.refreshRate_pos hτ i
  have hbar := H.meanRefreshRate_pos hτ
  have hlower := H.refreshRate_ge_third_mean hτ hτ1 i
  unfold refreshPotential
  constructor
  · apply (le_div_iff₀ ha).mpr
    linarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha)

theorem expected_refresh_occupation_le (H : HoldingFamily ι) (μ : ProbabilityVector ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (law (H.kernel τ hτ) μ n).mean (occupation (H.refreshRate τ) n) ≤
      (n:ℝ)*H.meanRefreshRate τ + 3 := by
  have h := occupation_mean_le (H.kernel τ hτ) μ (H.refreshRate τ) (H.refreshPotential τ)
    (H.meanRefreshRate τ) (-3) 0 (H.refreshPotential_poisson hτ) (H.refreshPotential_bounds hτ hτ1) n
  linarith

end
end Tournament.HoldingFamily
