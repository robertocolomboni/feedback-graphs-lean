module

public import Tournament.Model.EstimateUpdate
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem exp_neg_le_quadratic (z : ℝ) (hz : |z|≤1) : Real.exp (-z)≤1-z+z^2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -z) (by simpa only [abs_neg] using hz)
  have hu := (abs_le.mp h).2
  nlinarith

def trajectory (π₀ : ProbabilityVector ι) (η : ℝ) (g : ℕ → ι → ℝ) : ℕ → ProbabilityVector ι
  | 0 => π₀
  | n+1 => Model.exponentialUpdate (trajectory π₀ η g n) η (g n)

theorem trajectory_pos (π₀ : ProbabilityVector ι) (hπ : ∀ i, 0<π₀ i) (η : ℝ) (g : ℕ → ι → ℝ)
    (n : ℕ) (i : ι) : 0<trajectory π₀ η g n i := by
  induction n with
  | zero => exact hπ i
  | succ n ih =>
    exact div_pos (mul_pos ih (Real.exp_pos _)) (Model.exponentialNormalizer_pos _ _ _)

def normalizer (π : ProbabilityVector ι) (η : ℝ) (g : ι → ℝ) : ℝ :=
  π.mean (fun i ↦ Real.exp (-η*g i))

theorem normalizer_le (π : ProbabilityVector ι) (η : ℝ) (g : ι → ℝ) (hg : ∀ i, |η*g i|≤1) :
    normalizer π η g≤1-η*π.mean g+η^2*π.squareNorm g := by
  calc
    _ ≤ π.mean (fun i ↦ 1-η*g i+(η*g i)^2) := by
      apply π.mean_mono
      intro i
      simpa only [neg_mul] using exp_neg_le_quadratic (η*g i) (hg i)
    _ = _ := by
      have hfun : (fun i ↦ 1-η*g i+(η*g i)^2)=(fun i ↦ (1-η*g i)+η^2*(g i)^2) := by
        funext i
        ring
      rw [hfun,ProbabilityVector.mean_add,ProbabilityVector.mean_sub,ProbabilityVector.mean_const,
        ProbabilityVector.mean_const_mul,ProbabilityVector.mean_const_mul]
      rfl

theorem logNormalizer_le (π : ProbabilityVector ι) (η : ℝ) (g : ι → ℝ) (hg : ∀ i, |η*g i|≤1) :
    Real.log (normalizer π η g)≤-η*π.mean g+η^2*π.squareNorm g := by
  have hp : 0<normalizer π η g := Model.exponentialNormalizer_pos π η g
  have hlog := Real.log_le_sub_one_of_pos hp
  have hz := normalizer_le π η g hg
  linarith

theorem logUpdate (π : ProbabilityVector ι) (hπ : ∀ i, 0<π i) (η : ℝ) (g : ι → ℝ) (i : ι) :
    Real.log (Model.exponentialUpdate π η g i)=Real.log (π i)-η*g i-Real.log (normalizer π η g) := by
  change Real.log (π i*Real.exp (-η*g i)/normalizer π η g)=_
  unfold normalizer
  rw [Real.log_div (ne_of_gt (mul_pos (hπ i) (Real.exp_pos _)))
    (ne_of_gt (Model.exponentialNormalizer_pos π η g)),
    Real.log_mul (ne_of_gt (hπ i)) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
  ring

theorem logTrajectory (π₀ : ProbabilityVector ι) (hπ : ∀ i, 0<π₀ i) (η : ℝ) (g : ℕ → ι → ℝ)
    (n : ℕ) (i : ι) :
    Real.log (trajectory π₀ η g n i)=Real.log (π₀ i)-η*(∑ b ∈ Finset.range n, g b i)-
      ∑ b ∈ Finset.range n, Real.log (normalizer (trajectory π₀ η g b) η (g b)) := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    change Real.log (Model.exponentialUpdate (trajectory π₀ η g n) η (g n) i)=_
    rw [logUpdate _ (trajectory_pos π₀ hπ η g n) η (g n) i,ih]
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    ring

theorem second_order_from_initial (π₀ : ProbabilityVector ι) (hπ : ∀ i, 0<π₀ i)
    (η : ℝ) (hη : 0<η) (g : ℕ → ι → ℝ) (n : ℕ)
    (hg : ∀ b ∈ Finset.range n, ∀ i, |η*g b i|≤1) (i : ι) :
    (∑ b ∈ Finset.range n, ((trajectory π₀ η g b).mean (g b)-g b i))≤
      -Real.log (π₀ i)/η+η*(∑ b ∈ Finset.range n, (trajectory π₀ η g b).squareNorm (g b)) := by
  have hlog := Real.log_nonpos (le_of_lt (trajectory_pos π₀ hπ η g n i))
    ((trajectory π₀ η g n).weight_le_one i)
  rw [logTrajectory π₀ hπ η g n i] at hlog
  have hnorm : (∑ b ∈ Finset.range n, Real.log (normalizer (trajectory π₀ η g b) η (g b)))≤
      -η*(∑ b ∈ Finset.range n, (trajectory π₀ η g b).mean (g b))+
        η^2*(∑ b ∈ Finset.range n, (trajectory π₀ η g b).squareNorm (g b)) := by
    calc
      _ ≤ ∑ b ∈ Finset.range n, (-η*(trajectory π₀ η g b).mean (g b)+
          η^2*(trajectory π₀ η g b).squareNorm (g b)) :=
        Finset.sum_le_sum (fun b hb ↦ logNormalizer_le _ η (g b) (hg b hb))
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  calc
    _ ≤ (-Real.log (π₀ i)+η^2*(∑ b ∈ Finset.range n, (trajectory π₀ η g b).squareNorm (g b)))/η := by
      apply (le_div_iff₀ hη).mpr
      nlinarith
    _ = _ := by field_simp

def uniform [Nonempty ι] : ProbabilityVector ι where
  weight _ := 1/(Fintype.card ι:ℝ)
  nonneg _ := by positivity
  sum_eq_one := by
    have hcard : (Fintype.card ι:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

theorem uniform_pos [Nonempty ι] (i : ι) : 0<uniform (ι := ι) i := by
  change 0<1/(Fintype.card ι:ℝ)
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem uniform_log [Nonempty ι] (i : ι) : Real.log (uniform (ι := ι) i)=-Real.log (Fintype.card ι:ℝ) := by
  change Real.log (1/(Fintype.card ι:ℝ))=_
  rw [Real.log_div (by norm_num) (by exact_mod_cast Fintype.card_ne_zero),Real.log_one,zero_sub]

theorem second_order [Nonempty ι] (η : ℝ) (hη : 0<η) (g : ℕ → ι → ℝ) (n : ℕ)
    (hg : ∀ b ∈ Finset.range n, η*‖g b‖≤1) (i : ι) :
    (∑ b ∈ Finset.range n, ((trajectory uniform η g b).mean (g b)-g b i))≤
      Real.log (Fintype.card ι:ℝ)/η+
        η*(∑ b ∈ Finset.range n, (trajectory uniform η g b).squareNorm (g b)) := by
  have hcoord : ∀ b ∈ Finset.range n, ∀ j, |η*g b j|≤1 := by
    intro b hb j
    rw [abs_mul,abs_of_pos hη]
    have hj : |g b j|≤‖g b‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (g b) j
    exact le_trans (mul_le_mul_of_nonneg_left hj hη.le) (hg b hb)
  have h := second_order_from_initial uniform uniform_pos η hη g n hcoord i
  rwa [uniform_log,neg_neg] at h

theorem comparison_pairing (π : ProbabilityVector ι) (g : ι → ℝ) (i : ι) :
    (∑ j, (π j-(if j=i then 1 else 0))*g j)=π.mean g-g i := by
  simp [sub_mul,Finset.sum_sub_distrib,ProbabilityVector.mean]

theorem second_order_pairings [Nonempty ι] (η : ℝ) (hη : 0<η) (g : ℕ → ι → ℝ) (n : ℕ)
    (hg : ∀ b ∈ Finset.range n, η*‖g b‖≤1) (i : ι) :
    (∑ b ∈ Finset.range n, ∑ j, ((trajectory uniform η g b) j-(if j=i then 1 else 0))*g b j)≤
      Real.log (Fintype.card ι:ℝ)/η+
        η*(∑ b ∈ Finset.range n, (trajectory uniform η g b).squareNorm (g b)) := by
  simp_rw [comparison_pairing]
  exact second_order η hη g n hg i

end
end Tournament.Upper.ExponentialWeights
