module

public import Tournament.Model.MeasurableSensor

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι Seed B Z : Type*} [MeasurableSpace ι] [MeasurableSpace Seed]
variable [MeasurableSpace B] [MeasurableSpace Z]

def historyExtensionEquiv (n : ℕ) :
    ((Seed × (SensorHistory ι (B × Z) n × (ι × B))) × Z) ≃ᵐ
      (Seed × SensorHistory ι (B × Z) (n+1)) where
  toFun p := (p.1.1,Fin.snoc p.1.2.1 (p.1.2.2.1,(p.1.2.2.2,p.2)))
  invFun q := ((q.1,(Fin.init q.2,((q.2 (Fin.last n)).1,(q.2 (Fin.last n)).2.1))),
    (q.2 (Fin.last n)).2.2)
  left_inv p := by simp only [Fin.init_snoc,Fin.snoc_last]
  right_inv q := by simp only [Prod.mk.eta,Fin.snoc_init_self]
  measurable_toFun := by
    apply measurable_fst.fst.prodMk
    exact measurable_snoc _ _ (measurable_fst.comp (measurable_snd.comp measurable_fst))
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  measurable_invFun := by
    have hinit : Measurable (fun q : Seed × SensorHistory ι (B × Z) (n+1) ↦ Fin.init q.2) :=
      Measurable.of_eval (fun t ↦ (measurable_pi_apply t.castSucc).comp measurable_snd)
    have hlast : Measurable (fun q : Seed × SensorHistory ι (B × Z) (n+1) ↦ q.2 (Fin.last n)) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_snd
    exact (measurable_fst.prodMk (hinit.prodMk (hlast.fst.prodMk hlast.snd.fst))).prodMk hlast.snd.snd

variable [DiscreteMeasurableSpace ι] [Fintype ι]

def adjoinChosenAction (π : Learner ι Seed) (d : ℕ → ι × (B × Z) → ι → ℝ) (n : ℕ)
    (p : (Seed × SensorHistory ι (B × Z) n) × B) :
    Seed × (SensorHistory ι (B × Z) n × (ι × B)) :=
  (p.1.1,(p.1.2,(π.choose n (p.1.1,decodeHistory d n p.1.2),p.2)))

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem adjoinChosenAction_measurable (π : Learner ι Seed) (d : ℕ → ι × (B × Z) → ι → ℝ)
    (hd : ∀ n, Measurable (d n)) (n : ℕ) : Measurable (adjoinChosenAction π d n) := by
  have ha : Measurable (fun p : (Seed × SensorHistory ι (B × Z) n) × B ↦
      π.choose n (p.1.1,decodeHistory d n p.1.2)) :=
    (π.measurable_choose n).comp (measurable_fst.fst.prodMk
      ((decodeHistory_measurable d hd n).comp measurable_fst.snd))
  exact measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (ha.prodMk measurable_snd))

theorem adjoinChosenAction_embedding (π : Learner ι Seed) (d : ℕ → ι × (B × Z) → ι → ℝ)
    (hd : ∀ n, Measurable (d n)) (n : ℕ) : MeasurableEmbedding (adjoinChosenAction π d n) := by
  have hrange : Set.range (adjoinChosenAction π d n)=
      {h | h.2.2.1=π.choose n (h.1,decodeHistory d n h.2.1)} := by
    ext h
    constructor
    · rintro ⟨p,rfl⟩
      rfl
    · intro hh
      refine ⟨((h.1,h.2.1),h.2.2.2),?_⟩
      change (h.1,(h.2.1,(π.choose n (h.1,decodeHistory d n h.2.1),h.2.2.2)))=h
      rw [← hh]
  apply MeasurableEmbedding.of_measurable_inverse (adjoinChosenAction_measurable π d hd n)
    (g := fun h ↦ ((h.1,h.2.1),h.2.2.2))
  · rw [hrange]
    have ha : Measurable (fun h : Seed × (SensorHistory ι (B × Z) n × (ι × B)) ↦
        π.choose n (h.1,decodeHistory d n h.2.1)) :=
      (π.measurable_choose n).comp (measurable_fst.prodMk
        ((decodeHistory_measurable d hd n).comp measurable_snd.fst))
    exact measurableSet_eq_fun measurable_snd.snd.fst ha
  · exact (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.snd
  · intro p
    rfl

end
end Tournament.Model.MeasurableGame
