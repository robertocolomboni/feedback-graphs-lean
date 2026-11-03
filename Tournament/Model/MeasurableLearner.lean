module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι Seed Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Seed] [MeasurableSpace Ω]

abbrev History (ι : Type*) (t : ℕ) := Fin t → ι × (ι → ℝ)

structure Learner (ι Seed : Type*) [MeasurableSpace ι] [MeasurableSpace Seed] where
  choose : (t : ℕ) → Seed × History ι t → ι
  measurable_choose : ∀ t, Measurable (choose t)

def graphRecord (E : ι → ι → Prop) (a : ι) (loss : ι → ℝ) (v : ι) : ℝ :=
  if E a v then loss v else 0

theorem graphRecord_measurable [DiscreteMeasurableSpace ι] (E : ι → ι → Prop) :
    Measurable (fun p : ι × (ι → ℝ) ↦ graphRecord E p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  apply Measurable.ite
  · exact (MeasurableSet.of_discrete (s := {a : ι | E a v})).preimage measurable_fst
  · exact (measurable_pi_apply v).comp measurable_snd
  · exact measurable_const

theorem measurable_snoc {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] {t : ℕ}
    (h : X → Fin t → A) (x : X → A) (hh : Measurable h) (hx : Measurable x) :
    Measurable (fun ω ↦ (Fin.snoc (h ω) (x ω) : Fin (t+1) → A)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.snoc_last] using hx
  · simpa only [Fin.snoc_castSucc,Function.comp_def] using (measurable_pi_apply j).comp hh

def runHistory (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ) :
    (t : ℕ) → Seed × Ω → History ι t
  | 0 => fun _ i ↦ Fin.elim0 i
  | t+1 => fun ω ↦
      let h := runHistory π E loss t ω
      let a := π.choose t (ω.1,h)
      Fin.snoc h (a,graphRecord E a (loss t ω.2))

def action (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ)
    (t : ℕ) (ω : Seed × Ω) : ι := π.choose t (ω.1,runHistory π E loss t ω)

theorem runHistory_measurable [DiscreteMeasurableSpace ι]
    (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t, Measurable (loss t)) (t : ℕ) : Measurable (runHistory π E loss t) := by
  induction t with
  | zero =>
    apply Measurable.of_eval
    intro i
    exact Fin.elim0 i
  | succ t ih =>
    have ha := (π.measurable_choose t).comp (measurable_fst.prodMk ih)
    have ho := (graphRecord_measurable E).comp (ha.prodMk ((hloss t).comp measurable_snd))
    exact measurable_snoc _ _ ih (ha.prodMk ho)

theorem action_measurable [DiscreteMeasurableSpace ι]
    (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t, Measurable (loss t)) (t : ℕ) : Measurable (action π E loss t) :=
  (π.measurable_choose t).comp (measurable_fst.prodMk (runHistory_measurable π E loss hloss t))

omit [MeasurableSpace Ω] in
theorem runHistory_snoc (π : Learner ι Seed) (E : ι → ι → Prop)
    (loss : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Seed × Ω) :
    runHistory π E loss (t+1) ω=Fin.snoc (runHistory π E loss t ω)
      (action π E loss t ω,graphRecord E (action π E loss t ω) (loss t ω.2)) := rfl

omit [MeasurableSpace Ω] in

theorem histories_equal_of_past_feedback (π : Learner ι Seed) (E : ι → ι → Prop)
    (loss loss' : ℕ → Ω → ι → ℝ) (t : ℕ) (ω ω' : Seed × Ω) (hseed : ω.1=ω'.1)
    (hobs : ∀ s, s<t → graphRecord E (action π E loss s ω) (loss s ω.2)=
      graphRecord E (action π E loss s ω) (loss' s ω'.2)) :
    runHistory π E loss t ω=runHistory π E loss' t ω' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun s hs ↦ hobs s (by omega))
    have ha : action π E loss t ω=action π E loss' t ω' := by simp only [action,hseed,hh]
    rw [runHistory_snoc,runHistory_snoc,← ha,← hobs t (by omega),hh]

omit [MeasurableSpace Ω] in
theorem action_equal_of_past_feedback (π : Learner ι Seed) (E : ι → ι → Prop)
    (loss loss' : ℕ → Ω → ι → ℝ) (t : ℕ) (ω ω' : Seed × Ω) (hseed : ω.1=ω'.1)
    (hobs : ∀ s, s<t → graphRecord E (action π E loss s ω) (loss s ω.2)=
      graphRecord E (action π E loss s ω) (loss' s ω'.2)) :
    action π E loss t ω=action π E loss' t ω' := by
  have hh := histories_equal_of_past_feedback π E loss loss' t ω ω' hseed hobs
  simp only [action,hseed,hh]

end
end Tournament.Model.MeasurableGame
