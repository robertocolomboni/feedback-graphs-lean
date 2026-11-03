module

public import Tournament.Model.MeasurableLearner

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι Seed Ω Y : Type*} [MeasurableSpace ι] [MeasurableSpace Seed]
variable [MeasurableSpace Ω] [MeasurableSpace Y]

abbrev SensorHistory (ι Y : Type*) (t : ℕ) := Fin t → ι × Y

def decodeHistory (d : ℕ → ι × Y → ι → ℝ) (t : ℕ) (h : SensorHistory ι Y t) : History ι t :=
  fun q ↦ ((h q).1,d q.val (h q))

theorem decodeHistory_measurable (d : ℕ → ι × Y → ι → ℝ) (hd : ∀ t, Measurable (d t)) (t : ℕ) :
    Measurable (decodeHistory d t) := by
  apply Measurable.of_eval
  intro q
  exact (measurable_fst.comp (measurable_pi_apply q)).prodMk ((hd q.val).comp (measurable_pi_apply q))

omit [MeasurableSpace ι] [MeasurableSpace Seed] [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem decodeHistory_snoc (d : ℕ → ι × Y → ι → ℝ) (t : ℕ) (h : SensorHistory ι Y t) (a : ι) (y : Y) :
    decodeHistory d (t+1) (Fin.snoc h (a,y))=Fin.snoc (decodeHistory d t h) (a,d t (a,y)) := by
  funext q
  refine Fin.lastCases ?_ (fun u ↦ ?_) q
  · simp only [decodeHistory,Fin.snoc_last,Fin.val_last]
  · simp only [decodeHistory,Fin.snoc_castSucc,Fin.val_castSucc]

def runSensor (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ) (signal : ℕ → Ω × ι → Y) :
    (t : ℕ) → Seed × Ω → SensorHistory ι Y t
  | 0 => fun _ q ↦ Fin.elim0 q
  | t+1 => fun ω ↦
      let h := runSensor π d signal t ω
      let a := π.choose t (ω.1,decodeHistory d t h)
      Fin.snoc h (a,signal t (ω.2,a))

def sensorAction (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ) (signal : ℕ → Ω × ι → Y)
    (t : ℕ) (ω : Seed × Ω) : ι := π.choose t (ω.1,decodeHistory d t (runSensor π d signal t ω))

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem runSensor_entry (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ) (signal : ℕ → Ω × ι → Y)
    (t : ℕ) (q : Fin t) (ω : Seed × Ω) :
    runSensor π d signal t ω q=(sensorAction π d signal q.val ω,signal q.val (ω.2,sensorAction π d signal q.val ω)) := by
  induction t with
  | zero => exact Fin.elim0 q
  | succ t ih =>
    refine Fin.lastCases ?_ (fun u ↦ ?_) q
    · simp only [runSensor,Fin.snoc_last,Fin.val_last,sensorAction]
    · simpa only [runSensor,Fin.snoc_castSucc,Fin.val_castSucc] using ih _

theorem runSensor_measurable (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ)
    (hd : ∀ t, Measurable (d t)) (signal : ℕ → Ω × ι → Y)
    (hSignal : ∀ t, Measurable (signal t)) (t : ℕ) : Measurable (runSensor π d signal t) := by
  induction t with
  | zero =>
    apply Measurable.of_eval
    intro q
    exact Fin.elim0 q
  | succ t ih =>
    have ha : Measurable (sensorAction π d signal t) :=
      (π.measurable_choose t).comp
        (measurable_fst.prodMk ((decodeHistory_measurable d hd t).comp ih))
    exact measurable_snoc _ _ ih (ha.prodMk ((hSignal t).comp (measurable_snd.prodMk ha)))

theorem sensorAction_measurable (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ)
    (hd : ∀ t, Measurable (d t)) (signal : ℕ → Ω × ι → Y)
    (hSignal : ∀ t, Measurable (signal t)) (t : ℕ) : Measurable (sensorAction π d signal t) :=
  (π.measurable_choose t).comp
    (measurable_fst.prodMk ((decodeHistory_measurable d hd t).comp (runSensor_measurable π d hd signal hSignal t)))

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem decoded_runSensor (π : Learner ι Seed) (E : ι → ι → Prop)
    (d : ℕ → ι × Y → ι → ℝ) (signal : ℕ → Ω × ι → Y) (loss : ℕ → Ω → ι → ℝ)
    (t : ℕ) (hValid : ∀ s, s<t → ∀ ω a, d s (a,signal s (ω,a))=graphRecord E a (loss s ω))
    (ω : Seed × Ω) : decodeHistory d t (runSensor π d signal t ω)=runHistory π E loss t ω := by
  induction t with
  | zero =>
    funext q
    exact Fin.elim0 q
  | succ t ih =>
    have hh := ih (fun s hs ↦ hValid s (by omega))
    have ha : sensorAction π d signal t ω=action π E loss t ω := by
      simp only [sensorAction,action,hh]
    change decodeHistory d (t+1) (Fin.snoc (runSensor π d signal t ω)
      (sensorAction π d signal t ω,signal t (ω.2,sensorAction π d signal t ω)))=_
    rw [decodeHistory_snoc,runHistory_snoc,hh,ha,hValid t (by omega)]

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem sensorAction_eq_action (π : Learner ι Seed) (E : ι → ι → Prop)
    (d : ℕ → ι × Y → ι → ℝ) (signal : ℕ → Ω × ι → Y) (loss : ℕ → Ω → ι → ℝ)
    (t : ℕ) (hValid : ∀ s, s<t → ∀ ω a, d s (a,signal s (ω,a))=graphRecord E a (loss s ω))
    (ω : Seed × Ω) : sensorAction π d signal t ω=action π E loss t ω := by
  simp only [sensorAction,action,decoded_runSensor π E d signal loss t hValid ω]

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem runSensor_equal_of_past_signals (π : Learner ι Seed) (d : ℕ → ι × Y → ι → ℝ)
    (signal : ℕ → Ω × ι → Y) (t : ℕ) (ω ω' : Seed × Ω) (hseed : ω.1=ω'.1)
    (hSignal : ∀ s, s<t → ∀ a, signal s (ω.2,a)=signal s (ω'.2,a)) :
    runSensor π d signal t ω=runSensor π d signal t ω' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun s hs ↦ hSignal s (by omega))
    have ha : sensorAction π d signal t ω=sensorAction π d signal t ω' := by
      simp only [sensorAction,hseed,hh]
    change (Fin.snoc (runSensor π d signal t ω)
      (sensorAction π d signal t ω,signal t (ω.2,sensorAction π d signal t ω)) : SensorHistory ι Y (t+1))=
      (Fin.snoc (runSensor π d signal t ω')
      (sensorAction π d signal t ω',signal t (ω'.2,sensorAction π d signal t ω')) : SensorHistory ι Y (t+1))
    rw [hh,ha,hSignal t (by omega)]

end
end Tournament.Model.MeasurableGame
