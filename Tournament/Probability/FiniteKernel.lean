module

public import Tournament.Foundations.Centering
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

structure FiniteKernel (ι : Type*) [Fintype ι] where
  entry : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ entry i j
  row_sum : ∀ i, ∑ j, entry i j = 1

namespace FiniteKernel

instance : CoeFun (FiniteKernel ι) (fun _ ↦ ι → ι → ℝ) := ⟨entry⟩

def act (P : FiniteKernel ι) (f : ι → ℝ) (i : ι) : ℝ := ∑ j, P i j * f j

def Reversible (P : FiniteKernel ι) (p : ProbabilityVector ι) : Prop :=
  ∀ i j, p i * P i j = p j * P j i

def Stationary (P : FiniteKernel ι) (p : ProbabilityVector ι) : Prop :=
  ∀ j, ∑ i, p i * P i j = p j

def edgeSum (P : FiniteKernel ι) (p : ProbabilityVector ι) (f : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (p i * P i j) * f i j

def weightedInner (p : ProbabilityVector ι) (f g : ι → ℝ) : ℝ :=
  p.mean (fun i ↦ f i * g i)

theorem reversible_stationary (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Reversible p) : P.Stationary p := by
  intro j
  calc
    (∑ i, p i * P i j) = ∑ i, p j * P j i := by
      exact Finset.sum_congr rfl (fun i _ ↦ h i j)
    _ = p j := by rw [← Finset.mul_sum, P.row_sum, mul_one]

def row (P : FiniteKernel ι) (i : ι) : ProbabilityVector ι where
  weight := P i
  nonneg := P.nonneg i
  sum_eq_one := P.row_sum i

theorem stationary_mean_act (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Stationary p) (f : ι → ℝ) : p.mean (P.act f) = p.mean f := by
  unfold ProbabilityVector.mean act
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i, p i * (P i j * f j)) = (∑ i, p i * P i j) * f j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p j * f j := by rw [h j]

theorem row_switch_probability [DecidableEq ι] (P : FiniteKernel ι) (i : ι) :
    (P.row i).mean (fun j ↦ if j = i then 0 else 1) = 1 - P i i := by
  change (∑ j, P i j * (if j=i then 0 else 1)) = _
  have heq : (fun j ↦ P i j * (if j=i then (0:ℝ) else 1)) =
      (fun j ↦ P i j - (if j=i then P i j else 0)) := by
    funext j
    split <;> simp
  rw [heq, Finset.sum_sub_distrib, P.row_sum]
  simp

@[simp] theorem act_one (P : FiniteKernel ι) : P.act (fun _ ↦ 1) = fun _ ↦ 1 := by
  funext i
  simp [act, P.row_sum]

theorem edgeSum_add (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (f g : ι → ι → ℝ) :
    P.edgeSum p (fun i j ↦ f i j + g i j) = P.edgeSum p f + P.edgeSum p g := by
  simp [edgeSum, mul_add, Finset.sum_add_distrib]

theorem edgeSum_sub (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (f g : ι → ι → ℝ) :
    P.edgeSum p (fun i j ↦ f i j - g i j) = P.edgeSum p f - P.edgeSum p g := by
  simp [edgeSum, mul_sub, Finset.sum_sub_distrib]

theorem edgeSum_source (P : FiniteKernel ι) (p : ProbabilityVector ι) (f : ι → ℝ) :
    P.edgeSum p (fun i _ ↦ f i) = p.mean f := by
  unfold edgeSum ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (p i * P i j) * f i) = ∑ j, (p i * f i) * P i j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = p i * f i := by rw [← Finset.mul_sum, P.row_sum, mul_one]

theorem edgeSum_swap (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Reversible p) (f : ι → ι → ℝ) :
    P.edgeSum p (fun i j ↦ f j i) = P.edgeSum p f := by
  unfold edgeSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [h i j]

theorem edgeSum_target (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (h : P.Reversible p) (f : ι → ℝ) :
    P.edgeSum p (fun _ j ↦ f j) = p.mean f := by
  rw [← P.edgeSum_source p f]
  exact P.edgeSum_swap p h (fun i _ ↦ f i)

theorem edgeSum_cross (P : FiniteKernel ι) (p : ProbabilityVector ι) (f g : ι → ℝ) :
    P.edgeSum p (fun i j ↦ f i * g j) = weightedInner p f (P.act g) := by
  unfold edgeSum weightedInner ProbabilityVector.mean act
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightedInner_sub (p : ProbabilityVector ι) (f g h : ι → ℝ) :
    weightedInner p f (fun i ↦ g i - h i) =
      weightedInner p f g - weightedInner p f h := by
  simp [weightedInner, ProbabilityVector.mean, mul_sub, Finset.sum_sub_distrib]

theorem dirichlet_identity (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (hr : P.Reversible p) (f g : ι → ℝ) :
    weightedInner p f (fun i ↦ g i - P.act g i) =
      (1 / 2) * P.edgeSum p (fun i j ↦ (f i - f j) * (g i - g j)) := by
  have hexpand :
      P.edgeSum p (fun i j ↦ (f i - f j) * (g i - g j)) =
        P.edgeSum p (fun i _ ↦ f i * g i) -
          P.edgeSum p (fun i j ↦ f i * g j) -
          P.edgeSum p (fun i j ↦ f j * g i) +
          P.edgeSum p (fun _ j ↦ f j * g j) := by
    calc
      _ = P.edgeSum p (fun i j ↦ f i * g i - f i * g j - f j * g i + f j * g j) := by
        congr 1
        funext i j
        ring
      _ = _ := by rw [edgeSum_add, edgeSum_sub, edgeSum_sub]
  rw [hexpand, P.edgeSum_source p, P.edgeSum_target p hr]
  rw [P.edgeSum_swap p hr (fun i j ↦ f i * g j), P.edgeSum_cross p]
  rw [weightedInner_sub]
  unfold weightedInner
  ring

end FiniteKernel
end Tournament
