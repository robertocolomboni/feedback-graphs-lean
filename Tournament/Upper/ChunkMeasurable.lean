module

public import Tournament.Model.ComparisonMeasurable

@[expose] public section

namespace Tournament.Upper.ScoreRule

open MeasureTheory Model
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace A]
variable {F : ι → ι → Prop} {P : A → FiniteKernel ι} {p : A → ProbabilityVector ι}

def DecoderMeasurable (R : (a : A) → ScoreRule F (P a) (p a)) : Prop :=
  ∀ n (s j : A → ι), Measurable s → Measurable j →
    ∀ obs : A → ι → ℝ, (∀ k, Measurable (fun a ↦ obs a k)) →
      Measurable (fun a ↦ (R a).decoder n (s a) (obs a) (j a))

theorem tournament_decoder_measurable
    (hF : IsTournament F) (hP : ∀ i j, Measurable (fun a ↦ P a i j))
    (hp : ∀ a i, 0<p a i) (hRev : ∀ a, (P a).Reversible (p a))
    (hHold : ∀ a i, 1/2≤P a i i) :
    DecoderMeasurable (fun a ↦ tournamentScoreRule F hF (P a) (p a) (hp a) (hRev a) (hHold a)) := by
  intro n s j hs hj obs hObs
  exact scoreFromComparisons_measurable F P hP s j hs hj obs hObs

omit [DiscreteMeasurableSpace ι] in
theorem observedSum_measurable (R : (a : A) → ScoreRule F (P a) (p a))
    (hD : DecoderMeasurable R) (M : ℝ) (n : ℕ)
    (hist : A → ComparisonHistory ι n) (hHist : Measurable hist) :
    Measurable (fun a ↦ (R a).observedSum M n (hist a)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hPast : Measurable (fun a ↦ (hist a).1.1) := measurable_fst.comp (measurable_fst.comp hHist)
    have hObs : Measurable (fun a ↦ (hist a).1.2) := measurable_snd.comp (measurable_fst.comp hHist)
    have hNext : Measurable (fun a ↦ (hist a).2) := measurable_snd.comp hHist
    have hCurrent : Measurable (fun a ↦ currentAction n (hist a).1.1) := (currentAction_measurable n).comp hPast
    have hBalance := ih (fun a ↦ (hist a).1.1) hPast
    have hScore := hD n (fun a ↦ currentAction n (hist a).1.1) (fun a ↦ (hist a).2) hCurrent hNext
      (fun a ↦ (hist a).1.2) (fun k ↦ (measurable_pi_apply k).comp hObs)
    have hStopped : Measurable (fun a ↦ if |(R a).observedSum M n (hist a).1.1|≤M-1 then
        (R a).decoder n (currentAction n (hist a).1.1) (hist a).1.2 (hist a).2 else 0) :=
      hScore.ite (measurableSet_le hBalance.norm measurable_const) measurable_const
    have hEq : (fun a ↦ (R a).observedSum M (n+1) (hist a))=
        fun a ↦ (R a).observedSum M n (hist a).1.1+
          (if |(R a).observedSum M n (hist a).1.1|≤M-1 then
            (R a).decoder n (currentAction n (hist a).1.1) (hist a).1.2 (hist a).2 else 0) := by
      funext a
      rcases hist a with ⟨⟨h,obs⟩,j⟩
      rfl
    rw [hEq]
    exact hBalance.add hStopped

theorem candidateWeight_measurable (R : (a : A) → ScoreRule F (P a) (p a))
    (hD : DecoderMeasurable R) (hP : ∀ i j, Measurable (fun a ↦ P a i j))
    (M : ℝ) (n : ℕ) (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) (j : ι) :
    Measurable (fun a ↦ (R a).candidateWeight M n (hist a) (obs a) j) := by
  have hCurrent : Measurable (fun a ↦ currentAction n (hist a)) := (currentAction_measurable n).comp hHist
  have hBalance := observedSum_measurable R hD M n hist hHist
  have hScore := hD n (fun a ↦ currentAction n (hist a)) (fun _ ↦ j) hCurrent measurable_const obs hObs
  have hStopped : Measurable (fun a ↦ if |(R a).observedSum M n (hist a)|≤M-1 then
      (R a).decoder n (currentAction n (hist a)) (obs a) j else 0) :=
    hScore.ite (measurableSet_le hBalance.norm measurable_const) measurable_const
  exact ((finiteKernel_value_measurable P hP (fun a ↦ currentAction n (hist a)) (fun _ ↦ j) hCurrent measurable_const).mul
    (measurable_const.add (measurable_const.mul (hBalance.add hStopped)))).div
      (measurable_const.add (measurable_const.mul hBalance))

theorem candidateValid_measurableSet (R : (a : A) → ScoreRule F (P a) (p a))
    (hD : DecoderMeasurable R) (hP : ∀ i j, Measurable (fun a ↦ P a i j))
    (M : ℝ) (n : ℕ) (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) :
    MeasurableSet {a | (R a).candidateValid M n (hist a) (obs a)} := by
  have hWeight (j : ι) := candidateWeight_measurable R hD hP M n hist hHist obs hObs j
  change MeasurableSet ({a | ∀ j, 0≤(R a).candidateWeight M n (hist a) (obs a) j} ∩
    {a | (∑ j, (R a).candidateWeight M n (hist a) (obs a) j)=1})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j ↦ measurableSet_le measurable_const (hWeight j))
  · exact measurableSet_eq_fun (Finset.measurable_sum _ (fun j _ ↦ hWeight j)) measurable_const

theorem observedRow_weight_measurable (R : (a : A) → ScoreRule F (P a) (p a))
    (hD : DecoderMeasurable R) (hP : ∀ i j, Measurable (fun a ↦ P a i j))
    (hp : ∀ j, Measurable (fun a ↦ p a j)) (M : ℝ) (n : ℕ)
    (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) (j : ι) :
    Measurable (fun a ↦ (R a).observedRow M n (hist a) (obs a) j) := by
  have hValid := candidateValid_measurableSet R hD hP M n hist hHist obs hObs
  have hWeight := candidateWeight_measurable R hD hP M n hist hHist obs hObs j
  have hEq : (fun a ↦ (R a).observedRow M n (hist a) (obs a) j)=
      fun a ↦ if (R a).candidateValid M n (hist a) (obs a) then
        (R a).candidateWeight M n (hist a) (obs a) j else p a j := by
    funext a
    by_cases h : (R a).candidateValid M n (hist a) (obs a) <;> simp [observedRow,h]
  rw [hEq]
  exact hWeight.ite hValid (hp j)

end
end Tournament.Upper.ScoreRule

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model
open scoped Classical
noncomputable section

variable {ι A : Type*} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace A]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace A] in
theorem rules_decoder_eq (S : SteeringParameters ι) (π : ProbabilityVector ι) (j : Fin (S.m+1))
    (n : ℕ) (s : ι) (obs : ι → ℝ) (k : ι) :
    (S.rules π j).decoder n s obs k=
      scoreFromComparisons S.tournament ((S.holding π).kernel (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j))
        s obs k := by
  rcases S with ⟨F,hF,T,m,hK,hT,hm,rounded⟩
  cases rounded <;> rfl

theorem rounded_rules_decoder_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1)) :
    ScoreRule.DecoderMeasurable (fun a ↦ S.rules (p a) j) := by
  intro n s k hs hk obs hObs
  simp only [rules_decoder_eq]
  exact scoreFromComparisons_measurable S.tournament _
    (rounded_holding_kernel_measurable S hRound p hp (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j))
    s k hs hk obs hObs

theorem rounded_observedRow_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1))
    (M : ℝ) (n : ℕ) (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) (k : ι) :
    Measurable (fun a ↦ (S.rules (p a) j).observedRow M n (hist a) (obs a) k) :=
  ScoreRule.observedRow_weight_measurable (fun a ↦ S.rules (p a) j)
    (rounded_rules_decoder_measurable S hRound p hp j)
    (rounded_holding_kernel_measurable S hRound p hp (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j))
    (rounded_holding_sampling_measurable S hRound p hp) M n hist hHist obs hObs k

end
end Tournament.Upper.SteeringParameters
