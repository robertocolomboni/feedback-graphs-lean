module

public import Tournament.Model.DeterministicExecution
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical
noncomputable section

universe u v
variable {ι : Type u} [MeasurableSpace ι]

structure Strategy (ι : Type u) [MeasurableSpace ι] where
  Seed : Type v
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  learner : @Learner ι Seed inferInstance seedSpace

def BoundedSequence (loss : ℕ → ι → ℝ) : Prop := ∀ t a, 0≤loss t a ∧ loss t a≤1

variable [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]

def Strategy.regret (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) : ℝ :=
  letI := σ.seedSpace
  deterministicExpectedRegret T σ.law σ.learner E loss

def Strategy.regretSet (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) : Set ℝ :=
  (σ.regret T E) '' {loss | BoundedSequence loss}

def Strategy.worstRegret (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) : ℝ :=
  sSup (σ.regretSet T E)

theorem Strategy.regret_bounds (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (hLoss : BoundedSequence loss) :
    -2*(T:ℝ)≤σ.regret T E loss ∧ σ.regret T E loss≤2*(T:ℝ) := by
  let := σ.seedSpace
  let := σ.probability
  have hI := deterministicPathRegret_integrable T σ.law σ.learner E loss hLoss
  have hp (seed : σ.Seed) :
      -2*(T:ℝ)≤deterministicPathRegret T σ.learner E loss seed ∧
        deterministicPathRegret T σ.learner E loss seed≤2*(T:ℝ) := by
    have h := pathRegret_norm_le T loss hLoss (fun t ↦ deterministicAction σ.learner E loss t seed)
    simpa only [deterministicPathRegret,neg_mul] using abs_le.mp h
  constructor
  · have h := integral_mono (μ := σ.law) (integrable_const (-2*(T:ℝ))) hI (fun seed ↦ (hp seed).1)
    simpa only [Strategy.regret,deterministicExpectedRegret,integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono (μ := σ.law) hI (integrable_const (2*(T:ℝ))) (fun seed ↦ (hp seed).2)
    simpa only [Strategy.regret,deterministicExpectedRegret,integral_const,probReal_univ,one_smul] using h

omit [DiscreteMeasurableSpace ι] in
theorem Strategy.regretSet_nonempty (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) :
    (σ.regretSet T E).Nonempty :=
  ⟨σ.regret T E (fun _ _ ↦ 0),⟨(fun _ _ ↦ 0),(fun _ _ ↦ by constructor <;> norm_num),rfl⟩⟩

theorem Strategy.regretSet_bddAbove (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) :
    BddAbove (σ.regretSet T E) := by
  refine ⟨2*(T:ℝ),?_⟩
  rintro r ⟨loss,hLoss,rfl⟩
  exact (σ.regret_bounds T E loss hLoss).2

theorem Strategy.regret_le_worst (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (hLoss : BoundedSequence loss) : σ.regret T E loss≤σ.worstRegret T E :=
  le_csSup (σ.regretSet_bddAbove T E) ⟨loss,hLoss,rfl⟩

omit [DiscreteMeasurableSpace ι] in
theorem Strategy.worstRegret_le (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) (B : ℝ)
    (h : ∀ loss, BoundedSequence loss → σ.regret T E loss≤B) : σ.worstRegret T E≤B := by
  apply csSup_le (σ.regretSet_nonempty T E)
  rintro r ⟨loss,hLoss,rfl⟩
  exact h loss hLoss

theorem Strategy.worstRegret_bounds (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) :
    -2*(T:ℝ)≤σ.worstRegret T E ∧ σ.worstRegret T E≤2*(T:ℝ) := by
  constructor
  · obtain ⟨r,loss,hLoss,rfl⟩ := σ.regretSet_nonempty T E
    exact (σ.regret_bounds T E loss hLoss).1.trans (σ.regret_le_worst T E loss hLoss)
  · exact σ.worstRegret_le T E _ (fun loss hLoss ↦ (σ.regret_bounds T E loss hLoss).2)

def constantStrategy (i : ι) : Strategy.{u,v} ι where
  Seed := ULift.{v} Unit
  seedSpace := ⊤
  law := @Measure.dirac (ULift.{v} Unit) ⊤ (ULift.up ())
  probability := by infer_instance
  learner := ⟨fun _ _ ↦ i,fun _ ↦ measurable_const⟩

omit [DiscreteMeasurableSpace ι] in
theorem constantStrategy_regret (i : ι) (T : ℕ) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (constantStrategy.{u,v} i).regret T E loss=pathRegret T loss (fun _ ↦ i) := by
  change (∫ _seed : ULift.{v} Unit, pathRegret T loss (fun _ ↦ i)
    ∂(@Measure.dirac (ULift.{v} Unit) ⊤ (ULift.up ())))=_
  simp

omit [DiscreteMeasurableSpace ι] in
theorem constantStrategy_worst_le (i : ι) (T : ℕ) (E : ι → ι → Prop) :
    (constantStrategy.{u,v} i).worstRegret T E≤(T:ℝ) := by
  apply Strategy.worstRegret_le
  intro loss hLoss
  rw [constantStrategy_regret]
  exact constant_action_regret_le_horizon T loss i
    (fun t _ a ↦ (hLoss t a).1) (fun t _ a ↦ (hLoss t a).2)

def minimax (T : ℕ) (E : ι → ι → Prop) : ℝ :=
  sInf (Set.range (fun σ : Strategy.{u,v} ι ↦ σ.worstRegret T E))

omit [DiscreteMeasurableSpace ι] in
theorem minimax_range_nonempty (T : ℕ) (E : ι → ι → Prop) :
    (Set.range (fun σ : Strategy.{u,v} ι ↦ σ.worstRegret T E)).Nonempty :=
  ⟨(constantStrategy (Classical.arbitrary ι)).worstRegret T E,⟨_,rfl⟩⟩

theorem minimax_range_bddBelow (T : ℕ) (E : ι → ι → Prop) :
    BddBelow (Set.range (fun σ : Strategy.{u,v} ι ↦ σ.worstRegret T E)) := by
  refine ⟨-2*(T:ℝ),?_⟩
  rintro r ⟨σ,rfl⟩
  exact (σ.worstRegret_bounds T E).1

theorem minimax_le_worst (σ : Strategy.{u,v} ι) (T : ℕ) (E : ι → ι → Prop) :
    minimax.{u,v} T E≤σ.worstRegret T E := csInf_le (minimax_range_bddBelow T E) ⟨σ,rfl⟩

theorem le_minimax (T : ℕ) (E : ι → ι → Prop) (B : ℝ)
    (h : ∀ σ : Strategy.{u,v} ι, ∃ loss, BoundedSequence loss ∧ B≤σ.regret T E loss) :
    B≤minimax.{u,v} T E := by
  apply le_csInf (minimax_range_nonempty T E)
  rintro r ⟨σ,rfl⟩
  obtain ⟨loss,hLoss,hB⟩ := h σ
  exact hB.trans (σ.regret_le_worst T E loss hLoss)

theorem minimax_le_horizon (T : ℕ) (E : ι → ι → Prop) : minimax.{u,v} T E≤(T:ℝ) :=
  (minimax_le_worst (constantStrategy (Classical.arbitrary ι)) T E).trans
    (constantStrategy_worst_le _ T E)

end
end Tournament.Model.MeasurableGame
