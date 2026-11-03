module

public import Tournament.Probability.FiniteKernel

@[expose] public section

namespace Tournament.FiniteKernel

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

theorem weightedInner_comm (p : ProbabilityVector ι) (f g : ι → ℝ) :
    weightedInner p f g=weightedInner p g f := by
  unfold weightedInner
  congr 1
  funext i
  exact mul_comm _ _

theorem weightedInner_self (p : ProbabilityVector ι) (f : ι → ℝ) :
    weightedInner p f f=p.squareNorm f := by
  simp only [weightedInner,ProbabilityVector.mean,ProbabilityVector.squareNorm,pow_two]

theorem weightedInner_add (p : ProbabilityVector ι) (f g h : ι → ℝ) :
    weightedInner p f (fun i ↦ g i+h i)=weightedInner p f g+weightedInner p f h := by
  simp only [weightedInner,mul_add,ProbabilityVector.mean_add]

theorem weightedInner_const_mul_right (p : ProbabilityVector ι) (c : ℝ) (f g : ι → ℝ) :
    weightedInner p f (fun i ↦ c*g i)=c*weightedInner p f g := by
  unfold weightedInner ProbabilityVector.mean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

theorem weightedInner_const_mul_left (p : ProbabilityVector ι) (c : ℝ) (f g : ι → ℝ) :
    weightedInner p (fun i ↦ c*f i) g=c*weightedInner p f g := by
  rw [weightedInner_comm,weightedInner_const_mul_right,weightedInner_comm p g f]

theorem weightedInner_const_left (p : ProbabilityVector ι) (c : ℝ) (f : ι → ℝ) :
    weightedInner p (fun _ ↦ c) f=c*p.mean f := by
  exact ProbabilityVector.mean_const_mul p c f

theorem weightedInner_const_right (p : ProbabilityVector ι) (f : ι → ℝ) (c : ℝ) :
    weightedInner p f (fun _ ↦ c)=p.mean f*c := by
  exact ProbabilityVector.mean_mul_const p f c

theorem weightedInner_sum_right {κ : Type*} (p : ProbabilityVector ι) (f : ι → ℝ)
    (s : Finset κ) (g : κ → ι → ℝ) :
    weightedInner p f (fun i ↦ ∑ k ∈ s, g k i)=∑ k ∈ s, weightedInner p f (g k) := by
  unfold weightedInner
  simp only [Finset.mul_sum,ProbabilityVector.mean_sum]

theorem weightedInner_act_selfadjoint (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (hr : P.Reversible p) (f g : ι → ℝ) :
    weightedInner p f (P.act g)=weightedInner p (P.act f) g := by
  rw [← P.edgeSum_cross p f g,weightedInner_comm p (P.act f) g,← P.edgeSum_cross p g f]
  calc
    _ = P.edgeSum p (fun i j ↦ g j*f i) := by
      unfold edgeSum
      exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
    _ = _ := P.edgeSum_swap p hr (fun i j ↦ g i*f j)

theorem weightedInner_iterate_selfadjoint (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (hr : P.Reversible p) (k : ℕ) (f g : ι → ℝ) :
    weightedInner p f ((P.act)^[k] g)=weightedInner p ((P.act)^[k] f) g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',P.weightedInner_act_selfadjoint p hr,ih]
    rw [← Function.iterate_succ_apply]

end Tournament.FiniteKernel
