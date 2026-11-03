module

public import Tournament.Upper.DyadicSecondMoment
public import Tournament.Probability.StateCorrelations
public import Tournament.Probability.ChunkCorrelations

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FiniteKernel FinitePath

noncomputable section

variable {ι : Type*} [Fintype ι]

def sourceError (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (i : ι) (f : ι → ℝ) (s : ι) : ℝ :=
  estimationError Ψ w s f i

theorem sourceError_centered (Ψ : ι → ι → ι → ℝ) (p w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ p w) (i : ι) (f : ι → ℝ) : p.mean (sourceError Ψ w i f)=0 :=
  estimationError_mean_zero Ψ p w hcal f i

theorem source_pair_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (i : ι) (f g : ι → ℝ) (d : ℕ) :
    weightedInner H.sampling (sourceError Ψ w i f) (((H.kernel τ hτ).act)^[d] (sourceError Ψ w i g))=
      ∑ j : H.CenteredIndex, (eigenMultiplier τ (H.eigenvalue j))^d*
        H.coordinate (sourceError Ψ w i f) j*H.coordinate (sourceError Ψ w i g) j := by
  rw [H.inner_coordinates,sourceError_centered Ψ H.sampling w hcal i f,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [H.kernel_iterate_coordinate]
  ring

theorem referenceChunkErrorMoment_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (loss : ℕ → ι → ℝ) (start n : ℕ) :
    referenceChunkErrorMoment (H.kernel τ hτ) H.sampling w Ψ loss start n=
      ∑ i, w i*(∑ j : H.CenteredIndex, GeometricPartition.quadratic (eigenMultiplier τ (H.eigenvalue j))
        (fun t ↦ H.coordinate (sourceError Ψ w i (loss t)) j) start (n+1)) := by
  unfold referenceChunkErrorMoment
  rw [ProbabilityVector.mean_squareNorm]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hfun : (fun hist : History ι n ↦ (referenceErrorEstimate Ψ w (fun t ↦ loss (start+t)) n hist i)^2)=
      (fun hist ↦ (∑ t ∈ Finset.range (n+1), sourceError Ψ w i (loss (start+t)) (stateAt n hist t))^2) := by
    funext hist
    rw [referenceErrorEstimate_eq_sum_errors]
    rfl
  rw [hfun,state_sum_square_mean (H.kernel τ hτ) H.sampling (H.kernel_reversible hτ) n
    (fun t ↦ sourceError Ψ w i (loss (start+t)))]
  simp_rw [source_pair_coordinates H hτ Ψ w hcal]
  unfold GeometricPartition.quadratic
  calc
    _ = ∑ t ∈ Finset.range (n+1), ∑ j : H.CenteredIndex, ∑ u ∈ Finset.range (n+1),
        (eigenMultiplier τ (H.eigenvalue j))^(Nat.dist t u)*H.coordinate (sourceError Ψ w i (loss (start+t))) j*
          H.coordinate (sourceError Ψ w i (loss (start+u))) j := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = ∑ j : H.CenteredIndex, ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        (eigenMultiplier τ (H.eigenvalue j))^(Nat.dist t u)*H.coordinate (sourceError Ψ w i (loss (start+t))) j*
          H.coordinate (sourceError Ψ w i (loss (start+u))) j := Finset.sum_comm
    _ = _ := rfl

theorem referenceErrorSum_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) :
    referenceErrorSum (H.kernel τ hτ) H.sampling w Ψ loss offset ns=
      ∑ i, w i*(∑ j : H.CenteredIndex, Restarts.chunkSum (fun start n ↦
        GeometricPartition.quadratic (eigenMultiplier τ (H.eigenvalue j))
          (fun t ↦ H.coordinate (sourceError Ψ w i (loss t)) j) start (n+1)) offset ns) := by
  have hfun : referenceChunkErrorMoment (H.kernel τ hτ) H.sampling w Ψ loss=
      (fun start n ↦ ∑ i, w i*(∑ j : H.CenteredIndex, GeometricPartition.quadratic
        (eigenMultiplier τ (H.eigenvalue j)) (fun t ↦ H.coordinate (sourceError Ψ w i (loss t)) j) start (n+1))) := by
    funext start n
    exact referenceChunkErrorMoment_coordinates H hτ Ψ w hcal loss start n
  unfold referenceErrorSum
  rw [hfun,Restarts.chunkSum_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Restarts.chunkSum_const_mul,Restarts.chunkSum_finset_sum]

def referenceCovariance (H : HoldingFamily ι) (τ : ℝ) (w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  ∑ i, w i*(∑ j : H.CenteredIndex, GeometricPartition.quadratic (spectralCorrelation τ (H.eigenvalue j))
    (fun t ↦ H.coordinate (sourceError Ψ w i (loss t)) j) offset h)

theorem partitionedReferenceError_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    partitionedReferenceError (H.kernel τ hτ) H.sampling w Ψ τ (le_of_lt hτ) hτ1 loss offset n=
      referenceCovariance H τ w Ψ loss offset (n+1) := by
  have hfun : (fun coins : Restarts.Coins n ↦ referenceErrorSum (H.kernel τ hτ) H.sampling w Ψ loss offset (Restarts.parts n coins))=
      (fun coins ↦ ∑ i, w i*(∑ j : H.CenteredIndex, Restarts.chunkSum (fun start k ↦
        GeometricPartition.quadratic (eigenMultiplier τ (H.eigenvalue j))
          (fun t ↦ H.coordinate (sourceError Ψ w i (loss t)) j) start (k+1)) offset (Restarts.parts n coins))) := by
    funext coins
    exact referenceErrorSum_coordinates H hτ Ψ w hcal loss offset (Restarts.parts n coins)
  unfold partitionedReferenceError referenceCovariance
  rw [hfun,ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityVector.mean_const_mul]
  congr 1
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Restarts.mean_chunkQuadratic (le_of_lt hτ) hτ1]
  rfl

theorem referenceErrorEnergy_coordinates (H : HoldingFamily ι) (m : ℕ)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ loss offset n=
      (DyadicRate.law m).mean (fun j ↦ referenceCovariance H (DyadicRate.rate m j) w Ψ loss offset (n+1)) := by
  unfold referenceErrorEnergy
  congr 1
  funext j
  exact partitionedReferenceError_coordinates H (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) Ψ w hcal loss offset n

end
end Tournament.Upper
