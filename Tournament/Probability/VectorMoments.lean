module

public import Tournament.Probability.FinitePath
public import Tournament.Foundations.WeightedInner

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators Classical

noncomputable section

variable {ι Ω S : Type*} [Fintype ι] [Fintype Ω] [Fintype S]

def vectorMean (μ : ProbabilityVector Ω) (X : Ω → ι → ℝ) (k : ι) : ℝ := μ.mean (fun x ↦ X x k)

omit [Fintype Ω] [Fintype S] in
theorem squareNorm_add (w : ProbabilityVector ι) (a b : ι → ℝ) :
    w.squareNorm (fun k ↦ a k+b k)=w.squareNorm a+w.squareNorm b+2*FiniteKernel.weightedInner w a b := by
  change w.mean (fun k ↦ (a k+b k)^2)=_
  have hp : (fun k ↦ (a k+b k)^2)=(fun k ↦ a k^2+b k^2+2*(a k*b k)) := funext (fun _ ↦ by ring)
  rw [hp,mean_add,mean_add,mean_const_mul]
  rfl

omit [Fintype Ω] [Fintype S] in
theorem squareNorm_sub (w : ProbabilityVector ι) (a b : ι → ℝ) :
    w.squareNorm (fun k ↦ a k-b k)=w.squareNorm a+w.squareNorm b-2*FiniteKernel.weightedInner w a b := by
  change w.mean (fun k ↦ (a k-b k)^2)=_
  have hp : (fun k ↦ (a k-b k)^2)=(fun k ↦ a k^2+b k^2-2*(a k*b k)) := funext (fun _ ↦ by ring)
  rw [hp,mean_sub,mean_add,mean_const_mul]
  rfl

omit [Fintype S] in
theorem mean_squareNorm (μ : ProbabilityVector Ω) (w : ProbabilityVector ι) (X : Ω → ι → ℝ) :
    μ.mean (fun x ↦ w.squareNorm (X x))=∑ k, w k*μ.mean (fun x ↦ (X x k)^2) := by
  unfold squareNorm
  rw [mean_sum]
  simp only [mean_const_mul]

omit [Fintype S] in
theorem mean_weightedInner (μ : ProbabilityVector Ω) (w : ProbabilityVector ι) (X : Ω → ι → ℝ) (a : ι → ℝ) :
    μ.mean (fun x ↦ FiniteKernel.weightedInner w (X x) a)=FiniteKernel.weightedInner w (μ.vectorMean X) a := by
  change μ.mean (fun x ↦ ∑ k, w k*(X x k*a k))=∑ k, w k*(μ.vectorMean X k*a k)
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mean_const_mul,mean_mul_const]
  rfl

omit [Fintype S] in
theorem mean_squareNorm_centered (μ : ProbabilityVector Ω) (w : ProbabilityVector ι)
    (X : Ω → ι → ℝ) (a : ι → ℝ) (ha : ∀ k, μ.mean (fun x ↦ X x k)=a k) :
    μ.mean (fun x ↦ w.squareNorm (fun k ↦ X x k-a k))=
      μ.mean (fun x ↦ w.squareNorm (X x))-w.squareNorm a := by
  have hfun : (fun x ↦ w.squareNorm (fun k ↦ X x k-a k))=
      (fun x ↦ w.squareNorm (X x)+w.squareNorm a-2*FiniteKernel.weightedInner w (X x) a) := by
    funext x
    exact w.squareNorm_sub (X x) a
  have hmean : μ.vectorMean X=a := funext ha
  rw [hfun,mean_sub,mean_add,mean_const,mean_const_mul,mean_weightedInner,hmean,FiniteKernel.weightedInner_self]
  ring

theorem independent_weightedInner_mean (μ : ProbabilityVector Ω) (ν : ProbabilityVector S)
    (w : ProbabilityVector ι) (X : Ω → ι → ℝ) (Y : S → ι → ℝ) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ FiniteKernel.weightedInner w (X xy.1) (Y xy.2))=
      FiniteKernel.weightedInner w (μ.vectorMean X) (ν.vectorMean Y) := by
  change (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ ∑ k, w k*(X xy.1 k*Y xy.2 k))=
    ∑ k, w k*(μ.vectorMean X k*ν.vectorMean Y k)
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mean_const_mul]
  congr 1
  rw [joint_mean]
  simp only [mean_const_mul]
  exact mean_mul_const μ (fun x ↦ X x k) (ν.mean (fun y ↦ Y y k))

theorem independent_squareNorm_add (μ : ProbabilityVector Ω) (ν : ProbabilityVector S) (w : ProbabilityVector ι)
    (X : Ω → ι → ℝ) (Y : S → ι → ℝ) (a b : ι → ℝ)
    (ha : ∀ k, μ.mean (fun x ↦ X x k)=a k) (hb : ∀ k, ν.mean (fun y ↦ Y y k)=b k) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ w.squareNorm (fun k ↦ X xy.1 k+Y xy.2 k))=
      μ.mean (fun x ↦ w.squareNorm (X x))+ν.mean (fun y ↦ w.squareNorm (Y y))+
        2*FiniteKernel.weightedInner w a b := by
  have hfun : (fun xy : Ω × S ↦ w.squareNorm (fun k ↦ X xy.1 k+Y xy.2 k))=
      (fun xy ↦ w.squareNorm (X xy.1)+w.squareNorm (Y xy.2)+2*FiniteKernel.weightedInner w (X xy.1) (Y xy.2)) := by
    funext xy
    exact w.squareNorm_add (X xy.1) (Y xy.2)
  have hsecond : (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ w.squareNorm (Y xy.2))=ν.mean (fun y ↦ w.squareNorm (Y y)) := by
    rw [joint_mean]
    change μ.mean (fun _ ↦ ν.mean (fun y ↦ w.squareNorm (Y y)))=ν.mean (fun y ↦ w.squareNorm (Y y))
    exact μ.mean_const _
  have hX : μ.vectorMean X=a := funext ha
  have hY : ν.vectorMean Y=b := funext hb
  rw [hfun,mean_add,mean_add,mean_const_mul,joint_first_mean μ (fun _ ↦ ν) (fun x ↦ w.squareNorm (X x)),
    hsecond,independent_weightedInner_mean,hX,hY]

theorem independent_secondMoment_excess (μ : ProbabilityVector Ω) (ν : ProbabilityVector S) (w : ProbabilityVector ι)
    (X : Ω → ι → ℝ) (Y : S → ι → ℝ) (a b : ι → ℝ)
    (ha : ∀ k, μ.mean (fun x ↦ X x k)=a k) (hb : ∀ k, ν.mean (fun y ↦ Y y k)=b k) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ w.squareNorm (fun k ↦ X xy.1 k+Y xy.2 k))-
        w.squareNorm (fun k ↦ a k+b k)=
      (μ.mean (fun x ↦ w.squareNorm (X x))-w.squareNorm a)+
        (ν.mean (fun y ↦ w.squareNorm (Y y))-w.squareNorm b) := by
  rw [independent_squareNorm_add μ ν w X Y a b ha hb,w.squareNorm_add]
  ring

end
end Tournament.ProbabilityVector
