module

public import Tournament.Upper.AdaptiveRegret

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def switchCharges (A : SteeringParameters ι) (n : ℕ → ℕ) (default : ι) (B b : ℕ)
    (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) : ℝ :=
  if h : b<B then blockInternalSwitches default (past (b+1) B (by omega) x).2+1 else 0

theorem adaptive_switch_sum (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (B : ℕ)
    (hn : ∀ b ∈ Finset.range B, n b+1≤horizon A.m) :
    let P := A.algorithm n loss hloss
    (∫ x, (switchCount (prefixHorizon (fun b ↦ n b+1) B) (A.actions n default B x):ℝ)
      ∂(P.execution B).toMeasure)≤(B:ℝ)+2*meanRate A.m*(prefixHorizon (fun b ↦ n b+1) B:ℝ) := by
  let P := A.algorithm n loss hloss
  let μ := (P.execution B).toMeasure
  let length := fun b ↦ n b+1
  have hblock (b : ℕ) (hb : b∈Finset.range B) :
      (∫ x, A.switchCharges n default B b x ∂μ)≤1+2*meanRate A.m*((n b:ℝ)+1) := by
    have hb' : b<B := Finset.mem_range.mp hb
    let fS := fun s : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) (b+1) ↦
      blockInternalSwitches default s.2+1
    have heq : A.switchCharges n default B b=(fun x ↦ fS (past (b+1) B (by omega) x)) := by
      funext x
      simp only [switchCharges,dite_eq_left hb']
      rfl
    rw [heq]
    change (∫ x, fS (past (b+1) B (by omega) x) ∂(law P.kernel B).toMeasure)≤_
    rw [integral_next P.kernel b B (by omega) fS]
    calc
      _ ≤ (law P.kernel b).mean (fun _ ↦ 1+2*meanRate A.m*((n b:ℝ)+1)) := by
        apply ProbabilityVector.mean_mono
        intro s
        exact (A.playedRow_guarantee n loss hloss default b (hn b hb) (P.distribution b s)).switches
      _ = _ := ProbabilityVector.mean_const _ _
  have hpoint (x : History (fun b ↦ DyadicBlockOutcome ι A.m (n b)) B) :
      (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)≤
        ∑ b ∈ Finset.range B, A.switchCharges n default B b x := by
    have hs := scheduledSwitches_cover length B (A.actions n default B x)
    have hsr : (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)≤
        ∑ b ∈ Finset.range B, ((switchCount (length b)
          (fun t ↦ A.actions n default B x (prefixHorizon length b+t)):ℝ)+1) := by
      exact_mod_cast hs
    calc
      _ ≤ _ := hsr
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        have hb' : b<B := Finset.mem_range.mp hb
        simp only [switchCharges,dite_eq_left hb']
        have hlocal := ScheduledExecution.scheduledSwitches_eq_local default length
          (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) b B hb' x
        exact congrArg (fun q : ℕ ↦ (q:ℝ)+1) hlocal
  have hInt := integral_mono_ae
    (Integrable.of_finite (μ := μ) (f := fun x ↦ (switchCount (prefixHorizon length B) (A.actions n default B x):ℝ)))
    (Integrable.of_finite (μ := μ) (f := fun x ↦ ∑ b ∈ Finset.range B, A.switchCharges n default B b x))
    (Eventually.of_forall hpoint)
  rw [integral_finsetSum _ (fun b _ ↦ Integrable.of_finite (μ := μ) (f := A.switchCharges n default B b))] at hInt
  calc
    _ ≤ ∑ b ∈ Finset.range B, ∫ x, A.switchCharges n default B b x ∂μ := hInt
    _ ≤ ∑ b ∈ Finset.range B, (1+2*meanRate A.m*((n b:ℝ)+1)) := Finset.sum_le_sum hblock
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
        ← Finset.mul_sum]
      have hlength : (∑ b ∈ Finset.range B, ((n b:ℝ)+1))=(prefixHorizon length B:ℝ) := by
        simp [prefixHorizon,length]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hlength
      rw [hlength]

end
end Tournament.Upper.SteeringParameters
