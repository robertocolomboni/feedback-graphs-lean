module

public import Tournament.Upper.BandErrors

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def estimatorMap (Ψ : ι → ι → ι → ℝ) (s : ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := applyEstimator Ψ s
  map_add' f g := by
    funext k
    simp only [applyEstimator,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    change (∑ j, Ψ s k j*(c*f j))=c*∑ j, Ψ s k j*f j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)

def centeringMap (w : ProbabilityVector ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := w.center
  map_add' f g := by
    funext k
    exact w.center_add f g k
  map_smul' c f := by
    funext k
    change c*f k-w.mean (fun j ↦ c*f j)=c*(f k-w.mean f)
    rw [ProbabilityVector.mean_const_mul]
    ring

def sourceErrorMap (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (i : ι) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := sourceError Ψ w i
  map_add' f g := by
    funext s
    change ((estimatorMap Ψ s) (f+g)) i-((centeringMap w) (f+g)) i=
      (((estimatorMap Ψ s) f) i-((centeringMap w) f) i)+
        (((estimatorMap Ψ s) g) i-((centeringMap w) g) i)
    rw [map_add,map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext s
    change ((estimatorMap Ψ s) (c • f)) i-((centeringMap w) (c • f)) i=
      c*(((estimatorMap Ψ s) f) i-((centeringMap w) f) i)
    rw [map_smul,map_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

def EstimatorKillsConstants (Ψ : ι → ι → ι → ℝ) : Prop := ∀ s i, ∑ j, Ψ s i j=0

theorem sourceError_finset_sum {β : Type*} (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (i : ι) (s : Finset β) (f : β → ι → ℝ) :
    sourceError Ψ w i (fun k ↦ ∑ b ∈ s, f b k)=(fun k ↦ ∑ b ∈ s, sourceError Ψ w i (f b) k) := by
  have hfun : (fun k ↦ ∑ b ∈ s, f b k)=∑ b ∈ s, f b := by funext k; simp only [Finset.sum_apply]
  change (sourceErrorMap Ψ w i) (fun k ↦ ∑ b ∈ s, f b k)=_
  rw [hfun,map_sum]
  funext k
  simp only [Finset.sum_apply]
  rfl

theorem sourceError_const (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (hkill : EstimatorKillsConstants Ψ) (i : ι) (c : ℝ) :
    sourceError Ψ w i (fun _ ↦ c)=0 := by
  funext s
  unfold sourceError estimationError applyEstimator ProbabilityVector.center
  rw [ProbabilityVector.mean_const,sub_self,sub_zero,← Finset.sum_mul,hkill s i,zero_mul]
  rfl

theorem sourceError_center (Ψ : ι → ι → ι → ℝ) (w p : ProbabilityVector ι)
    (hkill : EstimatorKillsConstants Ψ) (i : ι) (f : ι → ℝ) :
    sourceError Ψ w i (p.center f)=sourceError Ψ w i f := by
  change (sourceErrorMap Ψ w i) (f-(fun _ ↦ p.mean f))=(sourceErrorMap Ψ w i) f
  rw [map_sub]
  change sourceError Ψ w i f-sourceError Ψ w i (fun _ ↦ p.mean f)=sourceError Ψ w i f
  rw [sourceError_const Ψ w hkill,sub_zero]

end
end Tournament.Upper

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem coordinate_add (H : HoldingFamily ι) (f g : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (f+g) n=H.coordinate f n+H.coordinate g n := weightedInner_add _ _ _ _

theorem coordinate_smul (H : HoldingFamily ι) (c : ℝ) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (c • f) n=c*H.coordinate f n := weightedInner_const_mul_right _ _ _ _

def bandProjectMap (H : HoldingFamily ι) (b : ℕ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := H.bandProject b
  map_add' f g := by
    apply H.eq_of_mean_coordinates
    · rw [H.bandProject_centered]
      change 0=H.sampling.mean (fun i ↦ H.bandProject b f i+H.bandProject b g i)
      rw [ProbabilityVector.mean_add,H.bandProject_centered,H.bandProject_centered]
      ring
    · intro n
      rw [H.coordinate_add,H.bandProject_coordinate,H.bandProject_coordinate,H.bandProject_coordinate,H.coordinate_add]
      split <;> ring
  map_smul' c f := by
    change H.bandProject b (c • f)=c • H.bandProject b f
    apply H.eq_of_mean_coordinates
    · change H.sampling.mean (H.bandProject b (c • f))=H.sampling.mean (fun i ↦ c*H.bandProject b f i)
      rw [H.bandProject_centered,ProbabilityVector.mean_const_mul,H.bandProject_centered,mul_zero]
    · intro n
      rw [H.coordinate_smul,H.bandProject_coordinate,H.bandProject_coordinate,H.coordinate_smul]
      split <;> ring

theorem bandProject_finset_sum {β : Type*} (H : HoldingFamily ι) (b : ℕ) (s : Finset β) (f : β → ι → ℝ) :
    H.bandProject b (fun i ↦ ∑ j ∈ s, f j i)=(fun i ↦ ∑ j ∈ s, H.bandProject b (f j) i) := by
  have hfun : (fun i ↦ ∑ j ∈ s, f j i)=∑ j ∈ s, f j := by
    funext i
    simp only [Finset.sum_apply]
  change (H.bandProjectMap b) (fun i ↦ ∑ j ∈ s, f j i)=_
  rw [hfun,map_sum]
  funext i
  simp only [Finset.sum_apply]
  rfl

end
end Tournament.HoldingFamily
