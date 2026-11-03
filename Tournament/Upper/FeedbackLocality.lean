module

public import Tournament.Model.ComparisonLocality
public import Tournament.Model.FeedbackEW
public import Tournament.Model.ScheduledExecution
public import Tournament.Upper.BlockSwitches

@[expose] public section

namespace Tournament

open scoped Classical
open FinitePath

noncomputable section

namespace Upper

variable {ι : Type*}

def BlockObservationsAgree (F : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ)
    (default : ι) (offset : ℕ) (ns : List ℕ) (y : BlockOutcome ι ns) : Prop :=
  ∀ t < Restarts.totalRounds ns,
    Model.comparisonObservation F (blockActions default ns y t) (loss (offset+t)) =
      Model.comparisonObservation F (blockActions default ns y t) (loss' (offset+t))

theorem BlockObservationsAgree.head {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {offset n : ℕ} {ns : List ℕ} {y : BlockOutcome ι (n::ns)}
    (h : BlockObservationsAgree F loss loss' default offset (n::ns) y) :
    ∀ t < n+1, Model.comparisonObservation F (stateAt n y.1 t) (loss (offset+t)) =
      Model.comparisonObservation F (stateAt n y.1 t) (loss' (offset+t)) := by
  intro t ht
  have ht' : t < Restarts.totalRounds (n::ns) := by
    change t < n+1+Restarts.totalRounds ns
    omega
  simpa only [blockActions, Model.appendActions, ite_eq_left ht] using h t ht'

theorem BlockObservationsAgree.tail {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {offset n : ℕ} {ns : List ℕ} {y : BlockOutcome ι (n::ns)}
    (h : BlockObservationsAgree F loss loss' default offset (n::ns) y) :
    BlockObservationsAgree F loss loss' default (offset+(n+1)) ns y.2 := by
  intro t ht
  have ht' : n+1+t < Restarts.totalRounds (n::ns) := by
    change n+1+t < n+1+Restarts.totalRounds ns
    omega
  have hge : ¬n+1+t < n+1 := by omega
  have hh := h (n+1+t) ht'
  simp only [blockActions, Model.appendActions, ite_eq_right hge,
    Nat.add_sub_cancel_left] at hh
  simpa only [Nat.add_assoc] using hh

theorem recordBlockComparisons_eq_of_observations (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (ns : List ℕ) (offset : ℕ)
    (y : BlockOutcome ι ns)
    (hobs : BlockObservationsAgree F loss loss' default offset ns y) :
    recordBlockComparisons F loss offset ns y =
      recordBlockComparisons F loss' offset ns y := by
  induction ns generalizing offset with
  | nil => rfl
  | cons n ns ih =>
    have hpre : ∀ t < n,
        Model.comparisonObservation F (stateAt n y.1 t) (loss (offset+t)) =
          Model.comparisonObservation F (stateAt n y.1 t) (loss' (offset+t)) := by
      intro t ht
      exact hobs.head t (by omega)
    have hlast := hobs.head n (by omega)
    rw [stateAt_last] at hlast
    change ((Model.recordComparisons F (fun t ↦ loss (offset+t)) n y.1,
      Model.comparisonObservation F (lastState n y.1) (loss (offset+n))),
      recordBlockComparisons F loss (offset+(n+1)) ns y.2) = _
    rw [Model.recordComparisons_eq_of_observations F (fun t ↦ loss (offset+t))
      (fun t ↦ loss' (offset+t)) n y.1 hpre, hlast, ih _ y.2 hobs.tail]
    rfl

end Upper

namespace Model

open Upper

variable {ι : Type*} [Fintype ι]

theorem ResetComparisonPolicy.law_atom_eq_of_full_observations
    (P : ResetComparisonPolicy ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (ns : List ℕ) (offset : ℕ)
    (y : BlockOutcome ι ns)
    (hobs : BlockObservationsAgree F loss loss' default offset ns y) :
    P.law F loss offset ns y = P.law F loss' offset ns y := by
  induction ns generalizing offset with
  | nil => rfl
  | cons n ns ih =>
    change (P.chunk offset n).law F (fun t ↦ loss (offset+t)) n y.1 *
      P.law F loss (offset+(n+1)) ns y.2 = _
    rw [(P.chunk offset n).law_atom_eq_of_observations F (fun t ↦ loss (offset+t))
      (fun t ↦ loss' (offset+t)) n y.1 (fun t ht ↦ hobs.head t (by omega)),
      ih _ y.2 hobs.tail]
    rfl

theorem RestartComparisonPolicy.law_atom_eq_of_full_observations {m : ℕ}
    (P : RestartComparisonPolicy ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (offset n : ℕ)
    (y : DyadicBlockOutcome ι m n)
    (hobs : BlockObservationsAgree F loss loss' default offset
      (Restarts.parts n y.2.1) y.2.2) :
    P.law F loss offset n y = P.law F loss' offset n y := by
  change P.rates y.1 *
    ((Restarts.law (P.restart y.1) (P.restart_nonneg y.1) (P.restart_le_one y.1) n) y.2.1 *
      (P.chunks y.1).law F loss offset (Restarts.parts n y.2.1) y.2.2) = _
  rw [(P.chunks y.1).law_atom_eq_of_full_observations F loss loss' default
    (Restarts.parts n y.2.1) offset y.2.2 hobs]
  rfl

namespace FeedbackEW

variable [Nonempty ι] {m : ℕ}

def ObservationsAgree (F : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ)
    (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B) : Prop :=
  ∀ t < prefixHorizon (fun b ↦ n b+1) B,
    comparisonObservation F (ScheduledExecution.trajectory default (fun b ↦ n b+1)
      (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B x t) (loss t) =
    comparisonObservation F (ScheduledExecution.trajectory default (fun b ↦ n b+1)
      (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B x t) (loss' t)

omit [Fintype ι] [Nonempty ι] in
theorem ObservationsAgree.prefix {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {n : ℕ → ℕ} {B : ℕ}
    {x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) (B+1)}
    (h : ObservationsAgree F loss loss' default n (B+1) x) :
    ObservationsAgree F loss loss' default n B x.1 := by
  intro t ht
  have ht' : t < prefixHorizon (fun b ↦ n b+1) (B+1) := by
    rw [prefixHorizon_succ]
    omega
  simpa only [ScheduledExecution.trajectory, appendActions, ite_eq_left ht] using h t ht'

omit [Fintype ι] [Nonempty ι] in
theorem ObservationsAgree.last {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {n : ℕ → ℕ} {B : ℕ}
    {x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) (B+1)}
    (h : ObservationsAgree F loss loss' default n (B+1) x) :
    BlockObservationsAgree F loss loss' default (prefixHorizon (fun b ↦ n b+1) B)
      (Restarts.parts (n B) x.2.2.1) x.2.2.2 := by
  intro t ht
  rw [Restarts.parts_totalRounds] at ht
  have ht' : prefixHorizon (fun b ↦ n b+1) B+t <
      prefixHorizon (fun b ↦ n b+1) (B+1) := by
    rw [prefixHorizon_succ]
    omega
  have hge : ¬prefixHorizon (fun b ↦ n b+1) B+t <
      prefixHorizon (fun b ↦ n b+1) B := by omega
  simpa only [ScheduledExecution.trajectory, appendActions, ite_eq_right hge,
    Nat.add_sub_cancel_left] using h _ ht'

omit [Fintype ι] [Nonempty ι] in
theorem ObservationsAgree.past {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {n : ℕ → ℕ} {B : ℕ}
    {x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B}
    (h : ObservationsAgree F loss loss' default n B x) (b : ℕ) (hb : b ≤ B) :
    ObservationsAgree F loss loss' default n b (FiniteProcess.past b B hb x) := by
  intro t ht
  have ht' : t < prefixHorizon (fun b ↦ n b+1) B :=
    lt_of_lt_of_le ht (ScheduledExecution.prefixHorizon_mono _ b B hb)
  simpa only [ScheduledExecution.trajectory_past default (fun b ↦ n b+1)
    (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2)
    b B hb x t ht] using h t ht'

omit [Fintype ι] [Nonempty ι] in
theorem ObservationsAgree.block {F : ι → ι → Prop} {loss loss' : ℕ → ι → ℝ}
    {default : ι} {n : ℕ → ℕ} {B : ℕ}
    {x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B}
    (h : ObservationsAgree F loss loss' default n B x) (b : ℕ) (hb : b < B) :
    BlockObservationsAgree F loss loss' default (prefixHorizon (fun b ↦ n b+1) b)
      (Restarts.parts (n b) (FiniteProcess.past (b+1) B (by omega) x).2.2.1)
      (FiniteProcess.past (b+1) B (by omega) x).2.2.2 :=
  (h.past (b+1) (by omega)).last

omit [Fintype ι] [Nonempty ι] in

theorem observationsAgree_of_graph_observations [LinearOrder ι]
    (E : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ)
    (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B)
    (hobs : ∀ t < prefixHorizon (fun b ↦ n b+1) B,
      graphObservation E (ScheduledExecution.trajectory default (fun b ↦ n b+1)
        (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B x t) (loss t) =
      graphObservation E (ScheduledExecution.trajectory default (fun b ↦ n b+1)
        (fun b y ↦ blockActions default (Restarts.parts (n b) y.2.1) y.2.2) B x t) (loss' t)) :
    ObservationsAgree (selectedEdge E) loss loss' default n B x := by
  intro t ht
  rw [← selectedComparison_record, ← selectedComparison_record, hobs t ht]

omit [Nonempty ι] in
theorem output_eq_of_observations (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (n : ℕ → ℕ) (b : ℕ)
    (p : ProbabilityVector ι) (y : DyadicBlockOutcome ι m (n b))
    (hobs : BlockObservationsAgree F loss loss' default (prefixHorizon (fun b ↦ n b+1) b)
      (Restarts.parts (n b) y.2.1) y.2.2) :
    (P.algorithm F n loss).output b p y = (P.algorithm F n loss').output b p y := by
  change P.output p y.1 _ _ (recordBlockComparisons F loss _ _ _) = _
  rw [recordBlockComparisons_eq_of_observations F loss loss' default _ _ _ hobs]
  rfl

theorem distribution_eq_of_observations (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B)
    (hobs : ObservationsAgree F loss loss' default n B x) :
    (P.algorithm F n loss).distribution B x =
      (P.algorithm F n loss').distribution B x := by
  induction B with
  | zero => rfl
  | succ B ih =>
    change exponentialUpdate ((P.algorithm F n loss).distribution B x.1) P.rate
      ((P.algorithm F n loss).output B ((P.algorithm F n loss).distribution B x.1) x.2) = _
    rw [ih x.1 hobs.prefix,
      output_eq_of_observations P F loss loss' default n B _ x.2 hobs.last]
    rfl

omit [Nonempty ι] in
theorem row_atom_eq_of_full_observations (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (n : ℕ → ℕ) (b : ℕ)
    (p : ProbabilityVector ι) (y : DyadicBlockOutcome ι m (n b))
    (hobs : BlockObservationsAgree F loss loss' default (prefixHorizon (fun b ↦ n b+1) b)
      (Restarts.parts (n b) y.2.1) y.2.2) :
    (P.algorithm F n loss).row b p y = (P.algorithm F n loss').row b p y :=
  (P.policy p).law_atom_eq_of_full_observations F loss loss' default _ _ y hobs

theorem kernel_atom_eq_of_full_observations (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) (B+1))
    (hobs : ObservationsAgree F loss loss' default n (B+1) x) :
    (P.algorithm F n loss).kernel B x.1 x.2 =
      (P.algorithm F n loss').kernel B x.1 x.2 := by
  unfold AdaptiveEW.kernel
  rw [distribution_eq_of_observations P F loss loss' default n B x.1 hobs.prefix]
  exact row_atom_eq_of_full_observations P F loss loss' default n B _ x.2 hobs.last

theorem execution_atom_eq_of_observations (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (default : ι) (n : ℕ → ℕ) (B : ℕ)
    (x : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι m (n b)) B)
    (hobs : ObservationsAgree F loss loss' default n B x) :
    (P.algorithm F n loss).execution B x = (P.algorithm F n loss').execution B x := by
  induction B with
  | zero => rfl
  | succ B ih =>
    change (P.algorithm F n loss).execution B x.1 *
      (P.algorithm F n loss).kernel B x.1 x.2 = _
    rw [ih x.1 hobs.prefix,
      kernel_atom_eq_of_full_observations P F loss loss' default n B x hobs]
    rfl

end FeedbackEW
end Model
end
end Tournament
