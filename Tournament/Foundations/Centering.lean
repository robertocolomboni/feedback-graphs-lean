module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

structure ProbabilityVector (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_eq_one : ∑ i, weight i = 1

namespace ProbabilityVector

instance : CoeFun (ProbabilityVector ι) (fun _ ↦ ι → ℝ) := ⟨weight⟩

theorem nonempty (v : ProbabilityVector ι) : Nonempty ι := by
  classical
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.mp h
  simpa using v.sum_eq_one

theorem weight_le_one (v : ProbabilityVector ι) (i : ι) : v i ≤ 1 := by
  calc
    v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ ↦ v.nonneg j) (Finset.mem_univ i)
    _ = 1 := v.sum_eq_one

def mean (v : ProbabilityVector ι) (f : ι → ℝ) : ℝ := ∑ i, v i * f i

def center (v : ProbabilityVector ι) (f : ι → ℝ) : ι → ℝ :=
  fun i ↦ f i - v.mean f

def variance (v : ProbabilityVector ι) (f : ι → ℝ) : ℝ :=
  ∑ i, v i * (v.center f i) ^ 2

def squareNorm (v : ProbabilityVector ι) (f : ι → ℝ) : ℝ :=
  ∑ i, v i * (f i) ^ 2

theorem squareNorm_nonneg (v : ProbabilityVector ι) (f : ι → ℝ) :
    0 ≤ v.squareNorm f :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg (v.nonneg i) (sq_nonneg _))

theorem squareNorm_div (v : ProbabilityVector ι) (f : ι → ℝ) (c : ℝ) :
    v.squareNorm (fun i ↦ f i / c) = v.squareNorm f / c^2 := by
  simp only [squareNorm, div_pow, mul_div_assoc, Finset.sum_div]

@[simp] theorem mean_const (v : ProbabilityVector ι) (c : ℝ) :
    v.mean (fun _ ↦ c) = c := by
  simp [mean, ← Finset.sum_mul, v.sum_eq_one]

theorem mean_sub (v : ProbabilityVector ι) (f g : ι → ℝ) :
    v.mean (fun i ↦ f i - g i) = v.mean f - v.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_add (v : ProbabilityVector ι) (f g : ι → ℝ) :
    v.mean (fun i ↦ f i + g i) = v.mean f + v.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_const_mul (v : ProbabilityVector ι) (c : ℝ) (f : ι → ℝ) :
    v.mean (fun i ↦ c * f i) = c * v.mean f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_mul_const (v : ProbabilityVector ι) (f : ι → ℝ) (c : ℝ) :
    v.mean (fun i ↦ f i * c) = v.mean f * c := by
  simp only [mean, ← mul_assoc, ← Finset.sum_mul]

theorem mean_neg (v : ProbabilityVector ι) (f : ι → ℝ) :
    v.mean (fun i ↦ -f i) = -v.mean f := by
  simp only [mean, mul_neg, Finset.sum_neg_distrib]

theorem mean_sum {κ : Type*} (v : ProbabilityVector ι) (s : Finset κ) (f : κ → ι → ℝ) :
    v.mean (fun i ↦ ∑ k ∈ s, f k i) = ∑ k ∈ s, v.mean (f k) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem center_sum {κ : Type*} (v : ProbabilityVector ι) (s : Finset κ) (f : κ → ι → ℝ)
    (i : ι) :
    v.center (fun j ↦ ∑ k ∈ s, f k j) i = ∑ k ∈ s, v.center (f k) i := by
  simp only [center, mean_sum, Finset.sum_sub_distrib]

theorem mean_mono (v : ProbabilityVector ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    v.mean f ≤ v.mean g := by
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (h i) (v.nonneg i))

theorem mean_nonneg (v : ProbabilityVector ι) {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ v.mean f :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg (v.nonneg i) (h i))

theorem abs_mean_le (v : ProbabilityVector ι) (f : ι → ℝ) :
    |v.mean f| ≤ v.mean (fun i ↦ |f i|) := by
  calc
    |v.mean f| ≤ ∑ i, |v i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = v.mean (fun i ↦ |f i|) := by
      simp only [mean, abs_mul, abs_of_nonneg (v.nonneg _)]

@[simp] theorem mean_center (v : ProbabilityVector ι) (f : ι → ℝ) :
    v.mean (v.center f) = 0 := by
  change v.mean (fun i ↦ f i - v.mean f) = 0
  rw [mean_sub, mean_const, sub_self]

@[simp] theorem center_center (w v : ProbabilityVector ι) (f : ι → ℝ) :
    w.center (v.center f) = w.center f := by
  funext i
  change f i - v.mean f - w.mean (fun j ↦ f j - v.mean f) = f i - w.mean f
  rw [mean_sub, mean_const]
  ring

theorem variance_nonneg (v : ProbabilityVector ι) (f : ι → ℝ) :
    0 ≤ v.variance f := by
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (v.nonneg i) (sq_nonneg _))

theorem sum_sq_sub_eq_variance_add (v : ProbabilityVector ι)
    (f : ι → ℝ) (c : ℝ) :
    (∑ i, v i * (f i - c) ^ 2) = v.variance f + (v.mean f - c) ^ 2 := by
  calc
    (∑ i, v i * (f i - c) ^ 2) =
        ∑ i, (v i * (v.center f i) ^ 2 +
          2 * (v.mean f - c) * (v i * v.center f i) +
          v i * (v.mean f - c) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [center]
      ring
    _ = v.variance f + (v.mean f - c) ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      change v.variance f + 2 * (v.mean f - c) * v.mean (v.center f) +
        (∑ i, v i) * (v.mean f - c) ^ 2 = _
      rw [mean_center, v.sum_eq_one]
      ring

theorem variance_le_sum_sq_sub (v : ProbabilityVector ι)
    (f : ι → ℝ) (c : ℝ) :
    v.variance f ≤ ∑ i, v i * (f i - c) ^ 2 := by
  rw [sum_sq_sub_eq_variance_add]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem isLeast_weighted_square (v : ProbabilityVector ι) (f : ι → ℝ) :
    IsLeast (Set.range (fun c : ℝ ↦ ∑ i, v i * (f i - c) ^ 2))
      (v.variance f) := by
  constructor
  · exact ⟨v.mean f, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact v.variance_le_sum_sq_sub f c

theorem variance_le_mul_variance (v w : ProbabilityVector ι)
    (f : ι → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (hvw : ∀ i, v i ≤ c * w i) :
    v.variance f ≤ c * w.variance f := by
  calc
    v.variance f ≤ ∑ i, v i * (f i - w.mean f) ^ 2 :=
      v.variance_le_sum_sq_sub f (w.mean f)
    _ ≤ ∑ i, (c * w i) * (f i - w.mean f) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hvw i) (sq_nonneg _)
    _ = c * w.variance f := by
      simp only [variance, center, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ProbabilityVector
end Tournament
