module

public import Tournament.Upper.ChunkMeasurable

@[expose] public section

namespace Tournament.Upper

open MeasureTheory Model
open scoped Classical
noncomputable section

variable {ι : Type*} [MeasurableSpace ι]

instance blockTranscriptMeasurableSpace : (ns : List ℕ) → MeasurableSpace (BlockTranscript ι ns)
  | [] => ⊤
  | n::ns => @Prod.instMeasurableSpace (ComparisonHistory ι n × (ι → ℝ)) (BlockTranscript ι ns)
      (@Prod.instMeasurableSpace (ComparisonHistory ι n) (ι → ℝ) inferInstance inferInstance)
      (blockTranscriptMeasurableSpace ns)

variable {A : Type*} [MeasurableSpace A]

def EstimatorDecoderMeasurable (d : A → ι → (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ s : A → ι, Measurable s → ∀ obs : A → ι → ℝ,
    (∀ i, Measurable (fun a ↦ obs a i)) → ∀ k, Measurable (fun a ↦ d a (s a) (obs a) k)

theorem observedEstimate_measurable (d : A → ι → (ι → ℝ) → ι → ℝ)
    (hD : EstimatorDecoderMeasurable d) (n : ℕ)
    (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ i, Measurable (fun a ↦ obs a i)) (k : ι) :
    Measurable (fun a ↦ ScoreRule.observedEstimate (d a) n (hist a) (obs a) k) := by
  induction n generalizing obs with
  | zero => exact hD hist hHist obs hObs k
  | succ n ih =>
    have hPast : Measurable (fun a ↦ (hist a).1.1) := measurable_fst.comp (measurable_fst.comp hHist)
    have hPrev : Measurable (fun a ↦ (hist a).1.2) := measurable_snd.comp (measurable_fst.comp hHist)
    have hNext : Measurable (fun a ↦ (hist a).2) := measurable_snd.comp hHist
    have hSum := ih (fun a ↦ (hist a).1.1) hPast (fun a ↦ (hist a).1.2)
      (fun i ↦ (measurable_pi_apply i).comp hPrev)
    have hCurrent := hD (fun a ↦ (hist a).2) hNext obs hObs k
    have hEq : (fun a ↦ ScoreRule.observedEstimate (d a) (n+1) (hist a) (obs a) k)=
        fun a ↦ ScoreRule.observedEstimate (d a) n (hist a).1.1 (hist a).1.2 k+d a (hist a).2 (obs a) k := by
      funext a
      rcases hist a with ⟨⟨h,old⟩,j⟩
      rfl
    rw [hEq]
    exact hSum.add hCurrent

variable [Fintype ι] [DiscreteMeasurableSpace ι]
variable {F : ι → ι → Prop} {P : A → FiniteKernel ι} {p : A → ProbabilityVector ι}

omit [DiscreteMeasurableSpace ι] in
theorem decoderMeasurable_shift (R : (a : A) → ScoreRule F (P a) (p a))
    (hR : ScoreRule.DecoderMeasurable R) (offset : ℕ) :
    ScoreRule.DecoderMeasurable (fun a ↦ (R a).shift offset) := by
  intro n s j hs hj obs hObs
  exact hR (offset+n) s j hs hj obs hObs

omit [DiscreteMeasurableSpace ι] in
theorem blockObservedEstimate_measurable (R : (a : A) → ScoreRule F (P a) (p a))
    (hR : ScoreRule.DecoderMeasurable R) (d : A → ι → (ι → ℝ) → ι → ℝ)
    (hD : EstimatorDecoderMeasurable d) (M : ℝ) (ns : List ℕ) (offset : ℕ)
    (log : A → BlockTranscript ι ns) (hLog : Measurable log) (k : ι) :
    Measurable (fun a ↦ blockObservedEstimate (R a) (d a) M offset ns (log a) k) := by
  induction ns generalizing offset with
  | nil => exact measurable_const
  | cons n ns ih =>
    have hPast : Measurable (fun a ↦ (log a).1.1) := measurable_fst.comp (measurable_fst.comp hLog)
    have hObs : Measurable (fun a ↦ (log a).1.2) := measurable_snd.comp (measurable_fst.comp hLog)
    have hTail : Measurable (fun a ↦ (log a).2) := measurable_snd.comp hLog
    have hEstimate := observedEstimate_measurable d hD n (fun a ↦ (log a).1.1) hPast
      (fun a ↦ (log a).1.2) (fun i ↦ (measurable_pi_apply i).comp hObs) k
    have hScore := ScoreRule.observedSum_measurable (fun a ↦ (R a).shift offset)
      (decoderMeasurable_shift R hR offset) M n (fun a ↦ (log a).1.1) hPast
    have hRemainder := ih (offset+(n+1)) (fun a ↦ (log a).2) hTail
    exact (hEstimate.div (measurable_const.add (measurable_const.mul hScore))).add hRemainder

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem truncateEstimate_measurable (g : A → ι → ℝ) (hG : ∀ i, Measurable (fun a ↦ g a i)) (η : ℝ) :
    Measurable (fun a ↦ Model.truncateEstimate η (g a)) := by
  have hVec : Measurable g := Measurable.of_eval hG
  have hNorm : Measurable (fun a ↦ η*‖g a‖) := measurable_const.mul hVec.norm
  exact hVec.ite (measurableSet_le hNorm measurable_const) measurable_const

omit [DiscreteMeasurableSpace ι] in
theorem truncated_blockOutput_measurable (R : (a : A) → ScoreRule F (P a) (p a))
    (hR : ScoreRule.DecoderMeasurable R) (d : A → ι → (ι → ℝ) → ι → ℝ)
    (hD : EstimatorDecoderMeasurable d) (M η : ℝ) (ns : List ℕ) (offset : ℕ)
    (log : A → BlockTranscript ι ns) (hLog : Measurable log) :
    Measurable (fun a ↦ Model.truncateEstimate η (blockObservedEstimate (R a) (d a) M offset ns (log a))) :=
  truncateEstimate_measurable _ (blockObservedEstimate_measurable R hR d hD M ns offset log hLog) η

end
end Tournament.Upper
