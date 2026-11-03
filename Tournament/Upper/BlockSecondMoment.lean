module

public import Tournament.Probability.VectorMoments
public import Tournament.Upper.BlockUnbiasedness
public import Tournament.Upper.ChunkMeanEnergy

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def correctedChunkMomentExcess (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (start n : ℕ) : ℝ :=
  ((R.shift start).tiltedLaw (fun t ↦ loss (start+t)) (fun t ↦ hloss (start+t)) M hM n).mean
    (fun hist ↦ w.squareNorm (fun k ↦ referenceEstimate Ψ (fun t ↦ loss (start+t)) n hist k /
      (R.shift start).likelihood (fun t ↦ loss (start+t)) M n hist))-
        w.variance (blockLoss (fun t ↦ loss (start+t)) (n+1))

def referenceErrorEstimate (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n) (k : ι) : ℝ :=
  referenceEstimate Ψ loss n hist k-w.center (blockLoss loss (n+1)) k

def referenceChunkErrorMoment (P : FiniteKernel ι) (p w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (start n : ℕ) : ℝ :=
  (law P p n).mean (fun hist ↦ w.squareNorm (referenceErrorEstimate Ψ w (fun t ↦ loss (start+t)) n hist))

def referenceErrorSum (P : FiniteKernel ι) (p w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  Restarts.chunkSum (referenceChunkErrorMoment P p w Ψ loss) offset ns

theorem block_secondMoment_excess (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w) :
    ∀ ns offset, (blockLaw R loss hloss M hM offset ns).mean
      (fun outcome ↦ w.squareNorm (blockCorrectedEstimate R Ψ loss M offset ns outcome))-
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds ns)) =
          Restarts.chunkSum (correctedChunkMomentExcess R Ψ loss hloss M hM w) offset ns := by
  intro ns
  induction ns with
  | nil =>
    intro offset
    have hzero : blockLoss (fun t ↦ loss (offset+t)) 0=(fun _ ↦ (0:ℝ)) := by funext i; simp [blockLoss]
    have hfun : (fun outcome : BlockOutcome ι [] ↦ w.squareNorm (blockCorrectedEstimate R Ψ loss M offset [] outcome))=
        (fun _ ↦ (0:ℝ)) := by
      funext outcome
      simp [blockCorrectedEstimate,ProbabilityVector.squareNorm]
    change (blockLaw R loss hloss M hM offset []).mean _-w.variance (blockLoss (fun t ↦ loss (offset+t)) 0)=0
    rw [hfun,ProbabilityVector.mean_const,hzero]
    simp [ProbabilityVector.variance,ProbabilityVector.center]
  | cons n ns ih =>
    intro offset
    let headLaw := (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM n
    let tailLaw := blockLaw R loss hloss M hM (offset+(n+1)) ns
    let X : History ι n → ι → ℝ := fun hist k ↦ referenceEstimate Ψ (fun t ↦ loss (offset+t)) n hist k /
      (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n hist
    let Y := blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns
    let a := w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1))
    let b := w.center (blockLoss (fun t ↦ loss ((offset+(n+1))+t)) (Restarts.totalRounds ns))
    have ha : ∀ k, headLaw.mean (fun hist ↦ X hist k)=a k :=
      ((R.shift offset).chunk_estimate_moments (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM w Ψ hcal n).1
    have hb : ∀ k, tailLaw.mean (fun outcome ↦ Y outcome k)=b k :=
      blockCorrectedEstimate_mean R Ψ loss hloss M hM w hcal ns (offset+(n+1))
    have htail : tailLaw.mean (fun outcome ↦ w.squareNorm (Y outcome))-w.squareNorm b =
        Restarts.chunkSum (correctedChunkMomentExcess R Ψ loss hloss M hM w) (offset+(n+1)) ns :=
      ih (offset+(n+1))
    have hsplit : blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds (n::ns))=
        (fun i ↦ blockLoss (fun t ↦ loss (offset+t)) (n+1) i+
          blockLoss (fun t ↦ loss ((offset+(n+1))+t)) (Restarts.totalRounds ns) i) := by
      funext i
      exact blockLoss_append loss offset (n+1) (Restarts.totalRounds ns) i
    have hcenter : w.center (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds (n::ns)))=(fun k ↦ a k+b k) := by
      funext k
      rw [hsplit,ProbabilityVector.center_add]
    change (headLaw.joint (fun _ ↦ tailLaw)).mean (fun outcome : History ι n × BlockOutcome ι ns ↦
        w.squareNorm (fun k ↦ X outcome.1 k+Y outcome.2 k))-
      w.squareNorm (w.center (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds (n::ns)))) = _
    rw [hcenter,ProbabilityVector.independent_secondMoment_excess headLaw tailLaw w X Y a b ha hb,htail]
    rfl

theorem block_secondMoment_identity (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w) (ns : List ℕ) (offset : ℕ) :
    (blockLaw R loss hloss M hM offset ns).mean
      (fun outcome ↦ w.squareNorm (blockCorrectedEstimate R Ψ loss M offset ns outcome)) =
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds ns))+
          Restarts.chunkSum (correctedChunkMomentExcess R Ψ loss hloss M hM w) offset ns := by
  have h := block_secondMoment_excess R Ψ loss hloss M hM w hcal ns offset
  linarith

theorem correctedChunkMomentExcess_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w) (start n : ℕ) :
    correctedChunkMomentExcess R Ψ loss hloss M hM w start n ≤
      (4/3)*referenceChunkErrorMoment P p w Ψ loss start n+
        (1/3)*w.variance (blockLoss (fun t ↦ loss (start+t)) (n+1)) := by
  have hm := (R.shift start).chunk_estimate_moments (fun t ↦ loss (start+t))
    (fun t ↦ hloss (start+t)) M hM w Ψ hcal n
  have href := referenceEstimate_mean P p w (P.reversible_stationary p R.reversible) Ψ hcal
    (fun t ↦ loss (start+t)) n
  have hv := ProbabilityVector.mean_squareNorm_centered (law P p n) w
    (referenceEstimate Ψ (fun t ↦ loss (start+t)) n)
    (w.center (blockLoss (fun t ↦ loss (start+t)) (n+1))) href
  change referenceChunkErrorMoment P p w Ψ loss start n =
    (law P p n).mean (fun hist ↦ w.squareNorm (referenceEstimate Ψ (fun t ↦ loss (start+t)) n hist))-
      w.variance (blockLoss (fun t ↦ loss (start+t)) (n+1)) at hv
  unfold correctedChunkMomentExcess
  nlinarith [hm.2]

theorem block_secondMoment_decomposition_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w) (ns : List ℕ) (offset : ℕ) :
    (blockLaw R loss hloss M hM offset ns).mean
      (fun outcome ↦ w.squareNorm (blockCorrectedEstimate R Ψ loss M offset ns outcome)) ≤
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds ns))+
          (4/3)*referenceErrorSum P p w Ψ loss offset ns+(1/3)*chunkVariance w loss offset ns := by
  rw [block_secondMoment_identity R Ψ loss hloss M hM w hcal]
  have hsum : Restarts.chunkSum (correctedChunkMomentExcess R Ψ loss hloss M hM w) offset ns ≤
      (4/3)*referenceErrorSum P p w Ψ loss offset ns+(1/3)*chunkVariance w loss offset ns := by
    calc
      _ ≤ Restarts.chunkSum (fun start n ↦ (4/3)*referenceChunkErrorMoment P p w Ψ loss start n+
          (1/3)*w.variance (blockLoss (fun t ↦ loss (start+t)) (n+1))) offset ns :=
        Restarts.chunkSum_mono _ _ (fun start n ↦ correctedChunkMomentExcess_le R Ψ loss hloss M hM w hcal start n) ns offset
      _ = _ := by
        rw [Restarts.chunkSum_add,Restarts.chunkSum_const_mul,Restarts.chunkSum_const_mul]
        rfl
  linarith

end
end Tournament.Upper
