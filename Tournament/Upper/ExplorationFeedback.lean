module

public import Tournament.Upper.ExplorationBound

@[expose] public section

namespace Tournament.Upper.Exploration

open ShrinkingDartboard
open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

abbrev Feedback (ι : Type*) (n : ℕ) := Fin n → ι → ℝ

def clampedEstimate (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (obs : ι → ℝ) (q : Bool × D) : ι → ℝ :=
  estimate E D κ (fun i ↦ max (obs i) 0) q

omit [Fintype ι] [Nonempty ι] in
theorem clampedEstimate_nonneg (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (obs : ι → ℝ) (q : Bool × D) (i : ι) : 0≤clampedEstimate E D κ obs q i :=
  estimate_nonneg E D κ hκ _ (fun _ ↦ le_max_right _ _) q i

omit [Fintype ι] [Nonempty ι] in
theorem clampedEstimate_observation (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ)
    (loss : ι → ℝ) (hloss : ∀ i, 0≤loss i) (arm : ι) (q : Bool × D) :
    clampedEstimate E D κ (Model.graphObservation E (played D arm q) loss) q=estimate E D κ loss q := by
  have hObs : (fun i ↦ max (Model.graphObservation E (played D arm q) loss i) 0)=
      Model.graphObservation E (played D arm q) loss := by
    funext i
    apply max_eq_left
    unfold Model.graphObservation
    split_ifs
    · exact hloss i
    · exact le_rfl
  unfold clampedEstimate
  rw [hObs]
  funext i
  exact estimate_observable E D κ loss q arm i

def feedbackWeights (E : ι → ι → Prop) (D : Finset ι) (κ η : ℝ) :
    (n : ℕ) → History D n → Feedback ι n → ProbabilityVector ι
  | 0, _, _ => ExponentialWeights.uniform
  | n+1, h, obs => Model.exponentialUpdate (feedbackWeights E D κ η n h.1 (Fin.init obs)) η
      (clampedEstimate E D κ (obs (Fin.last n)) h.2.2)

def feedbackLatentRow (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ) (η : ℝ) (hη : 0≤η) :
    (n : ℕ) → History D n → Feedback ι n → ProbabilityVector ι
  | 0, _, _ => ExponentialWeights.uniform
  | n+1, h, obs => (ShrinkingDartboard.kernel (feedbackWeights E D κ η n h.1 (Fin.init obs)) η hη
      (clampedEstimate E D κ (obs (Fin.last n)) h.2.2)
      (clampedEstimate_nonneg E D κ hκ (obs (Fin.last n)) h.2.2)).row h.2.1

def feedbackRound (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (n : ℕ) (h : History D n) (obs : Feedback ι n) : ProbabilityVector (RoundOutcome D) :=
  (feedbackLatentRow E D κ hκ η hη n h obs).joint (fun _ ↦ law D κ hκ hκ1)

def feedbackRecord (E : ι → ι → Prop) (D : Finset ι) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → History D n → Feedback ι n
  | 0, _ => fun t ↦ Fin.elim0 t
  | n+1, h => Fin.snoc (feedbackRecord E D loss n h.1)
      (Model.graphObservation E (played D h.2.1 h.2.2) (loss n))

theorem feedbackWeights_record (E : ι → ι → Prop) (D : Finset ι) (κ η : ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (n : ℕ) (h : History D n) :
    feedbackWeights E D κ η n h (feedbackRecord E D loss n h)=processWeights E D κ η loss n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [feedbackWeights,feedbackRecord,Fin.init_snoc,Fin.snoc_last]
    rw [ih h.1,clampedEstimate_observation E D κ (loss n) (hloss n)]
    rfl

theorem feedbackLatentRow_record (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (η : ℝ) (hη : 0≤η) (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) :
    feedbackLatentRow E D κ hκ η hη n h (feedbackRecord E D loss n h)=latentRow E D κ hκ η hη loss hloss n h := by
  cases n with
  | zero => rfl
  | succ n =>
    apply ProbabilityVector.ext_weights
    intro j
    change (if h.2.1=j then keep η
        (clampedEstimate E D κ (feedbackRecord E D loss (n+1) h (Fin.last n)) h.2.2) h.2.1 else 0)+
      (1-keep η (clampedEstimate E D κ (feedbackRecord E D loss (n+1) h (Fin.last n)) h.2.2) h.2.1)*
        Model.exponentialUpdate (feedbackWeights E D κ η n h.1 (Fin.init (feedbackRecord E D loss (n+1) h))) η
          (clampedEstimate E D κ (feedbackRecord E D loss (n+1) h (Fin.last n)) h.2.2) j=
      (if h.2.1=j then keep η (estimate E D κ (loss n) h.2.2) h.2.1 else 0)+
        (1-keep η (estimate E D κ (loss n) h.2.2) h.2.1)*
          Model.exponentialUpdate (processWeights E D κ η loss n h.1) η (estimate E D κ (loss n) h.2.2) j
    simp only [feedbackRecord,Fin.init_snoc,Fin.snoc_last,feedbackWeights_record E D κ η loss hloss,
      clampedEstimate_observation E D κ (loss n) (hloss n)]

theorem feedbackRound_record (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (n : ℕ) (h : History D n) :
    feedbackRound E D κ hκ hκ1 η hη n h (feedbackRecord E D loss n h)=
      roundKernel E D κ hκ hκ1 η hη loss hloss n h := by
  unfold feedbackRound roundKernel
  rw [feedbackLatentRow_record E D κ hκ η hη loss hloss]

def feedbackExecution (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (T : ℕ) : ProbabilityVector (History D T) :=
  FiniteProcess.law (fun n h ↦ feedbackRound E D κ hκ hκ1 η hη n h (feedbackRecord E D loss n h)) T

theorem feedbackExecution_eq (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ) :
    feedbackExecution E D κ hκ hκ1 η hη loss T=execution E D κ hκ hκ1 η hη loss hloss T := by
  apply congrArg (fun row ↦ FiniteProcess.law row T)
  funext n h
  exact feedbackRound_record E D κ hκ hκ1 η hη loss hloss n h

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem observable_graph_feedback_upper (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (default : ι) :
    let κ := rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    let η := learningRate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
    ∃ hκ : 0<κ, ∃ hη : 0<η,
      (feedbackExecution E D κ hκ.le (by linarith) η hη.le loss T).mean
        (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
        (3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  rcases observable_graph_upper E D hD hK T hT hRate loss hloss default with ⟨hκ,hη,hBound⟩
  refine ⟨hκ,hη,?_⟩
  rwa [feedbackExecution_eq E D _ hκ.le _ _ hη.le loss (fun n i ↦ (hloss n i).1)]

end
end Tournament.Upper.Exploration
