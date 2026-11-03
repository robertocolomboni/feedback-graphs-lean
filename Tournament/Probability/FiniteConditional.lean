module

public import Tournament.Foundations.Centering
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Tournament.FiniteConditional

open scoped BigOperators Classical

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

noncomputable section

def DependsOn (info : Ω → S) (f : Ω → ℝ) : Prop :=
  ∀ ω ω', info ω = info ω' → f ω = f ω'

def fiberSum (μ : ProbabilityVector Ω) (info : Ω → S) (f : Ω → ℝ) (s : S) : ℝ :=
  ∑ ω, if info ω=s then μ ω*f ω else 0

def fiberMass (μ : ProbabilityVector Ω) (info : Ω → S) (s : S) : ℝ :=
  ∑ ω, if info ω=s then μ ω else 0

def MeanLE (μ : ProbabilityVector Ω) (info : Ω → S) (f : Ω → ℝ) (c : ℝ) : Prop :=
  ∀ s, fiberSum μ info f s ≤ c*fiberMass μ info s

theorem mean_fiber_expansion (μ : ProbabilityVector Ω) (info : Ω → S)
    (a : S → ℝ) (f : Ω → ℝ) :
    μ.mean (fun ω ↦ a (info ω)*f ω) = ∑ s, a s*fiberSum μ info f s := by
  unfold ProbabilityVector.mean fiberSum
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem mean_fiber_mass (μ : ProbabilityVector Ω) (info : Ω → S) (a : S → ℝ) :
    μ.mean (fun ω ↦ a (info ω)) = ∑ s, a s*fiberMass μ info s := by
  have h := mean_fiber_expansion μ info a (fun _ ↦ 1)
  simpa only [mul_one, fiberSum, fiberMass] using h

theorem mean_mul_of_fiber_bound (μ : ProbabilityVector Ω) (info : Ω → S)
    (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) (f : Ω → ℝ) (c : ℝ) (hf : MeanLE μ info f c) :
    μ.mean (fun ω ↦ a (info ω)*f ω) ≤ c*μ.mean (fun ω ↦ a (info ω)) := by
  rw [mean_fiber_expansion, mean_fiber_mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have h := mul_le_mul_of_nonneg_left (hf s) (ha s)
  nlinarith

def fiberValue (info : Ω → S) (f : Ω → ℝ) (s : S) : ℝ :=
  if hs : ∃ ω, info ω=s then f hs.choose else 0

omit [Fintype S] in
theorem fiberValue_on (info : Ω → S) (f : Ω → ℝ) (hf : DependsOn info f) (ω : Ω) :
    fiberValue info f (info ω) = f ω := by
  have hs : ∃ ω', info ω'=info ω := ⟨ω,rfl⟩
  rw [fiberValue, dite_eq_left hs]
  exact hf hs.choose ω hs.choose_spec

omit [Fintype S] in
theorem fiberValue_nonneg (info : Ω → S) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (s : S) :
    0 ≤ fiberValue info f s := by
  unfold fiberValue
  split
  · exact hf _
  · exact le_refl _

theorem mean_mul_le (μ : ProbabilityVector Ω) (info : Ω → S) (Z f : Ω → ℝ)
    (hZ : DependsOn info Z) (hZ0 : ∀ ω, 0 ≤ Z ω) (c : ℝ) (hf : MeanLE μ info f c) :
    μ.mean (fun ω ↦ Z ω*f ω) ≤ c*μ.mean Z := by
  have h := mean_mul_of_fiber_bound μ info (fiberValue info Z)
    (fiberValue_nonneg info Z hZ0) f c hf
  simpa only [fiberValue_on info Z hZ] using h

omit [Fintype S] in
theorem meanLE_add (μ : ProbabilityVector Ω) (info : Ω → S) (f g : Ω → ℝ) (a b : ℝ)
    (hf : MeanLE μ info f a) (hg : MeanLE μ info g b) :
    MeanLE μ info (fun ω ↦ f ω+g ω) (a+b) := by
  intro s
  have heq : fiberSum μ info (fun ω ↦ f ω+g ω) s = fiberSum μ info f s+fiberSum μ info g s := by
    unfold fiberSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    split <;> simp [mul_add]
  rw [heq]
  nlinarith [hf s, hg s]

omit [Fintype S] in
theorem meanLE_of_pointwise (μ : ProbabilityVector Ω) (info : Ω → S) (f : Ω → ℝ)
    (c : ℝ) (hf : ∀ ω, f ω ≤ c) : MeanLE μ info f c := by
  intro s
  unfold fiberSum fiberMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  split
  · nlinarith [mul_le_mul_of_nonneg_left (hf ω) (μ.nonneg ω)]
  · simp

end
end Tournament.FiniteConditional
