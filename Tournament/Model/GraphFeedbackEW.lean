module

public import Tournament.Model.GraphFeedback
public import Tournament.Model.FeedbackEW

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical
open Upper

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

structure GraphResetPolicy (ι : Type*) [Fintype ι] where
  chunk : ℕ → ℕ → GraphPolicy ι

def GraphResetPolicy.law (π : GraphResetPolicy ι) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (offset : ℕ) → (ns : List ℕ) → ProbabilityVector (BlockOutcome ι ns)
  | _, [] => ProbabilityVector.pure (ULift.up ())
  | offset, n::ns => ((π.chunk offset n).law E (fun t ↦ loss (offset+t)) n).joint
      (fun _ ↦ π.law E loss (offset+(n+1)) ns)

def ResetComparisonPolicy.toGraph (π : ResetComparisonPolicy ι) (E : ι → ι → Prop) : GraphResetPolicy ι where
  chunk offset n := (π.chunk offset n).toGraph E

theorem ResetComparisonPolicy.toGraph_law (π : ResetComparisonPolicy ι) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) : ∀ ns offset,
    (π.toGraph E).law E loss offset ns=π.law (selectedEdge E) loss offset ns := by
  intro ns
  induction ns with
  | nil => intro offset; rfl
  | cons n ns ih =>
    intro offset
    change (((π.chunk offset n).toGraph E).law E (fun t ↦ loss (offset+t)) n).joint
      (fun _ ↦ (π.toGraph E).law E loss (offset+(n+1)) ns)=
      ((π.chunk offset n).law (selectedEdge E) (fun t ↦ loss (offset+t)) n).joint
        (fun _ ↦ π.law (selectedEdge E) loss (offset+(n+1)) ns)
    rw [ComparisonPolicy.toGraph_law,ih]

structure GraphRestartPolicy (ι : Type*) [Fintype ι] (m : ℕ) where
  rates : ProbabilityVector (Fin (m+1))
  restart : Fin (m+1) → ℝ
  restart_nonneg : ∀ j, 0≤restart j
  restart_le_one : ∀ j, restart j≤1
  chunks : Fin (m+1) → GraphResetPolicy ι

def GraphRestartPolicy.law {m : ℕ} (π : GraphRestartPolicy ι m) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) : ProbabilityVector (DyadicBlockOutcome ι m n) :=
  π.rates.sigmaJoint (fun j ↦
    (Restarts.law (π.restart j) (π.restart_nonneg j) (π.restart_le_one j) n).sigmaJoint
      (fun coins ↦ (π.chunks j).law E loss offset (Restarts.parts n coins)))

def RestartComparisonPolicy.toGraph {m : ℕ} (π : RestartComparisonPolicy ι m)
    (E : ι → ι → Prop) : GraphRestartPolicy ι m where
  rates := π.rates
  restart := π.restart
  restart_nonneg := π.restart_nonneg
  restart_le_one := π.restart_le_one
  chunks j := (π.chunks j).toGraph E

theorem RestartComparisonPolicy.toGraph_law {m : ℕ} (π : RestartComparisonPolicy ι m)
    (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    (π.toGraph E).law E loss offset n=π.law (selectedEdge E) loss offset n := by
  apply ProbabilityVector.ext_weights
  intro y
  change π.rates y.1*((Restarts.law (π.restart y.1) (π.restart_nonneg y.1)
    (π.restart_le_one y.1) n) y.2.1*((π.chunks y.1).toGraph E).law E loss offset
      (Restarts.parts n y.2.1) y.2.2)=
    π.rates y.1*((Restarts.law (π.restart y.1) (π.restart_nonneg y.1)
      (π.restart_le_one y.1) n) y.2.1*(π.chunks y.1).law (selectedEdge E) loss offset
        (Restarts.parts n y.2.1) y.2.2)
  rw [ResetComparisonPolicy.toGraph_law]

def recordBlockGraph (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (offset : ℕ) → (ns : List ℕ) → BlockOutcome ι ns → BlockTranscript ι ns
  | _, [], _ => ULift.up ()
  | offset, n::ns, y =>
      ((recordGraph E (fun t ↦ loss (offset+t)) n y.1,
        graphObservation E (FinitePath.lastState n y.1) (loss (offset+n))),
          recordBlockGraph E loss (offset+(n+1)) ns y.2)

def translateBlock (E : ι → ι → Prop) : (ns : List ℕ) → BlockTranscript ι ns → BlockTranscript ι ns
  | [], _ => ULift.up ()
  | n::ns, log =>
      ((translateHistory E n log.1.1,selectedComparison E (currentAction n log.1.1) log.1.2),
        translateBlock E ns log.2)

omit [Fintype ι] in
theorem translateBlock_record (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    ∀ ns offset (y : BlockOutcome ι ns),
      translateBlock E ns (recordBlockGraph E loss offset ns y)=
        recordBlockComparisons (selectedEdge E) loss offset ns y := by
  intro ns
  induction ns with
  | nil => intro offset y; rfl
  | cons n ns ih =>
    intro offset y
    simp only [translateBlock,recordBlockGraph,recordBlockComparisons,translateHistory_record,
      recordGraph_current,selectedComparison_record,ih]

structure GraphFeedbackEW (ι : Type*) [Fintype ι] (m : ℕ) where
  rate : ℝ
  policy : ProbabilityVector ι → GraphRestartPolicy ι m
  output : ProbabilityVector ι → (j : Fin (m+1)) → (offset : ℕ) →
    (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ

def GraphFeedbackEW.algorithm [Nonempty ι] {m : ℕ} (P : GraphFeedbackEW ι m)
    (E : ι → ι → Prop) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) :
    AdaptiveEW (fun b ↦ DyadicBlockOutcome ι m (n b)) ι where
  rate := P.rate
  output b π y := P.output π y.1 (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1)
    (recordBlockGraph E loss (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1) y.2.2)
  row b π := (P.policy π).law E loss (prefixHorizon (fun b ↦ n b+1) b) (n b)

def FeedbackEW.toGraph {m : ℕ} (P : FeedbackEW ι m) (E : ι → ι → Prop) : GraphFeedbackEW ι m where
  rate := P.rate
  policy π := (P.policy π).toGraph E
  output π j offset ns log := P.output π j offset ns (translateBlock E ns log)

theorem FeedbackEW.toGraph_algorithm [Nonempty ι] {m : ℕ} (P : FeedbackEW ι m)
    (E : ι → ι → Prop) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) :
    (P.toGraph E).algorithm E n loss=P.algorithm (selectedEdge E) n loss := by
  have hrate : ((P.toGraph E).algorithm E n loss).rate=(P.algorithm (selectedEdge E) n loss).rate := rfl
  have houtput : ((P.toGraph E).algorithm E n loss).output=(P.algorithm (selectedEdge E) n loss).output := by
    funext b π y
    change P.output π y.1 _ _ (translateBlock E _ (recordBlockGraph E loss _ _ y.2.2))=
      P.output π y.1 _ _ (recordBlockComparisons (selectedEdge E) loss _ _ y.2.2)
    rw [translateBlock_record]
  have hrow : ((P.toGraph E).algorithm E n loss).row=(P.algorithm (selectedEdge E) n loss).row := by
    funext b π
    exact RestartComparisonPolicy.toGraph_law (P.policy π) E loss _ _
  cases hP : (P.toGraph E).algorithm E n loss with
  | mk rate output row =>
    cases hA : P.algorithm (selectedEdge E) n loss with
    | mk rate' output' row' =>
      have hr : rate=rate' := by simpa only [hP,hA] using hrate
      have ho : output=output' := by simpa only [hP,hA] using houtput
      have hk : row=row' := by simpa only [hP,hA] using hrow
      subst rate'
      subst output'
      subst row'
      rfl

end
end Tournament.Model
