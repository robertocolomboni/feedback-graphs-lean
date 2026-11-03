module

public import Tournament.Probability.UniformExecution
public import Tournament.Model.Minimax
public import Tournament.Model.RegretPrefix

@[expose] public section

namespace Tournament.Model.MeasurableGame.FiniteFeedback

open MeasureTheory ProbabilityTheory
open Tournament.Probability
open scoped Classical unitInterval
noncomputable section

universe u v
variable {ι : Type u} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable {Y : ℕ → Type v} [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
variable [∀ n, MeasurableSpace (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)]
variable [∀ n, StandardBorelSpace (Y n)]

abbrev Feedback (ι : Type*) (n : ℕ) := Fin n → ι → ℝ

def replay (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] :
    (n : ℕ) → UniformSeed.Space n × Feedback ι n → FiniteProcess.History Y n
  | 0, _ => ULift.up ()
  | n+1, q =>
      let obs := Fin.init q.2
      let h := replay κ n (Fin.init q.1,obs)
      (h,KernelSampler.draw (κ n) (h,obs) (q.1 (Fin.last n)))

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem replay_measurable
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : Measurable (replay κ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hSeed : Measurable (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦ Fin.init q.1) :=
      Measurable.of_eval (fun j ↦ (measurable_pi_apply j.castSucc).comp measurable_fst)
    have hObs : Measurable (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦ Fin.init q.2) :=
      Measurable.of_eval (fun j ↦ (measurable_pi_apply j.castSucc).comp measurable_snd)
    have hPast : Measurable (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦
        replay κ n (Fin.init q.1,Fin.init q.2)) := ih.comp (hSeed.prodMk hObs)
    have hFresh : Measurable (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦ q.1 (Fin.last n)) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_fst
    rw [← UniformExecution.history_succ_space (Y := Y) n]
    exact hPast.prodMk (KernelSampler.draw_measurable_comp (κ n)
      (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦
        (replay κ n (Fin.init q.1,Fin.init q.2),Fin.init q.2))
      (fun q : UniformSeed.Space (n+1) × Feedback ι (n+1) ↦ q.1 (Fin.last n))
      (hPast.prodMk hObs) hFresh)

def next (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) (q : UniformSeed.Space (n+1) × Feedback ι n) : Y n :=
  KernelSampler.draw (κ n) (replay κ n (Fin.init q.1,q.2),q.2) (q.1 (Fin.last n))

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem next_measurable
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : Measurable (next κ n) := by
  have hSeed : Measurable (fun q : UniformSeed.Space (n+1) × Feedback ι n ↦ Fin.init q.1) :=
    Measurable.of_eval (fun j ↦ (measurable_pi_apply j.castSucc).comp measurable_fst)
  exact KernelSampler.draw_measurable_comp (κ n)
    (fun q : UniformSeed.Space (n+1) × Feedback ι n ↦ (replay κ n (Fin.init q.1,q.2),q.2))
    (fun q : UniformSeed.Space (n+1) × Feedback ι n ↦ q.1 (Fin.last n))
    (((replay_measurable κ n).comp (hSeed.prodMk measurable_snd)).prodMk measurable_snd)
    ((measurable_pi_apply (Fin.last n)).comp measurable_fst)

def observations (n : ℕ) (h : History ι n) : Feedback ι n := fun i ↦ (h i).2

omit [DiscreteMeasurableSpace ι] in
theorem observations_measurable (n : ℕ) : Measurable (observations (ι := ι) n) :=
  Measurable.of_eval (fun i ↦ measurable_snd.comp (measurable_pi_apply i))

def learner
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (play : (n : ℕ) → Y n → ι) (T : ℕ) (default : ι) :
    Learner ι (UniformSeed.Space T) where
  choose n q := if hn : n<T then
    play n (next κ n (UniformSeed.take (n+1) T (by omega) q.1,observations n q.2)) else default
  measurable_choose n := by
    by_cases hn : n<T
    · simp only [dite_eq_left hn]
      exact (Measurable.of_discrete (f := play n)).comp
        ((next_measurable κ n).comp
          (((UniformSeed.take_measurable (n+1) T (by omega)).comp measurable_fst).prodMk
            ((observations_measurable n).comp measurable_snd)))
    · simp only [dite_eq_right hn]
      exact measurable_const

def record (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → FiniteProcess.History Y n → Feedback ι n
  | 0, _ => fun i ↦ Fin.elim0 i
  | n+1, h => Fin.snoc (record E play loss n h.1) (graphRecord E (play n h.2) (loss n))

def context (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι) (loss : ℕ → ι → ℝ)
    (n : ℕ) (h : FiniteProcess.History Y n) : FiniteProcess.History Y n × Feedback ι n :=
  (h,record E play loss n h)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [∀ n, Fintype (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)] in
theorem replay_record
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (n : ℕ) (ω : UniformSeed.Space n) :
    replay κ n (ω,record E play loss n (UniformExecution.run κ (context E play loss) n ω))=
      UniformExecution.run κ (context E play loss) n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [UniformExecution.run,record,replay,Fin.init_snoc]
    rw [ih (Fin.init ω)]
    rfl

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [∀ n, Fintype (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)] in
theorem next_record
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (n T : ℕ) (hn : n+1≤T) (ω : UniformSeed.Space T) :
    next κ n (UniformSeed.take (n+1) T hn ω,
      record E play loss n (UniformExecution.runPrefix κ (context E play loss) n T (by omega) ω))=
      (UniformExecution.runPrefix κ (context E play loss) (n+1) T hn ω).2 := by
  unfold next
  rw [UniformSeed.take_init]
  unfold UniformExecution.runPrefix
  rw [replay_record]
  rfl

omit [DiscreteMeasurableSpace ι] in
theorem choose_record
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι) (n : ℕ) (hn : n<T)
    (ω : UniformSeed.Space T) (pub : History ι n)
    (hPub : observations n pub=record E play loss n
      (UniformExecution.runPrefix κ (context E play loss) n T (by omega) ω)) :
    (learner κ play T default).choose n (ω,pub)=
      play n (UniformExecution.runPrefix κ (context E play loss) (n+1) T (by omega) ω).2 := by
  simp only [learner,dite_eq_left hn,hPub,next_record]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem observations_snoc (n : ℕ) (h : History ι n) (a : ι) (obs : ι → ℝ) :
    observations (n+1) (Fin.snoc h (a,obs))=Fin.snoc (observations n h) obs := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [observations]

omit [DiscreteMeasurableSpace ι] in
theorem execution_observations
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι) (n : ℕ) (hn : n≤T) (ω : UniformSeed.Space T) :
    observations n (runHistory (learner κ play T default) E (fun t (_ : Unit) ↦ loss t) n (ω,()))=
      record E play loss n (UniformExecution.runPrefix κ (context E play loss) n T hn ω) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    have hn' : n<T := by omega
    have hAction := choose_record κ E play loss T default n hn' ω _ (ih (by omega))
    have hPast : (UniformExecution.runPrefix κ (context E play loss) (n+1) T hn ω).1=
        UniformExecution.runPrefix κ (context E play loss) n T (by omega) ω := by
      simp only [UniformExecution.runPrefix,UniformExecution.run,UniformSeed.take_init]
    rw [runHistory_snoc,observations_snoc]
    simp only [action]
    rw [hAction,ih (by omega)]
    simp only [record,hPast]

omit [DiscreteMeasurableSpace ι] in
theorem execution_action
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι) (n : ℕ) (hn : n<T) (ω : UniformSeed.Space T) :
    deterministicAction (learner κ play T default) E loss n ω=
      play n (UniformExecution.runPrefix κ (context E play loss) (n+1) T (by omega) ω).2 :=
  choose_record κ E play loss T default n hn ω _
    (execution_observations κ E play loss T default n (by omega) ω)

def sampledActions (play : (n : ℕ) → Y n → ι) (default : ι) (T : ℕ)
    (h : FiniteProcess.History Y T) (t : ℕ) : ι :=
  if ht : t<T then play t (FiniteProcess.past (t+1) T (by omega) h).2 else default

omit [DiscreteMeasurableSpace ι] in
theorem execution_action_full
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι) (n : ℕ) (hn : n<T) (ω : UniformSeed.Space T) :
    deterministicAction (learner κ play T default) E loss n ω=
      sampledActions play default T (UniformExecution.run κ (context E play loss) T ω) n := by
  rw [execution_action κ E play loss T default n hn ω]
  simp only [sampledActions,dite_eq_left hn,UniformExecution.run_past]

variable [Fintype ι] [Nonempty ι]

omit [DiscreteMeasurableSpace ι] in
theorem execution_regret
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι) (ω : UniformSeed.Space T) :
    deterministicPathRegret T (learner κ play T default) E loss ω=
      pathRegret T loss (sampledActions play default T (UniformExecution.run κ (context E play loss) T ω)) := by
  apply pathRegret_eq_of_action_prefix
  intro t ht
  exact execution_action_full κ E play loss T default t ht ω

omit [DiscreteMeasurableSpace ι] in
theorem expected_regret_eq_mean
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι)
    (row : (n : ℕ) → FiniteProcess.History Y n → ProbabilityVector (Y n))
    (hRow : ∀ n h, κ n (context E play loss n h)=(row n h).toMeasure) :
    deterministicExpectedRegret T (UniformSeed.law T) (learner κ play T default) E loss=
      (FiniteProcess.law row T).mean (fun h ↦ pathRegret T loss (sampledActions play default T h)) := by
  unfold deterministicExpectedRegret
  calc
    _ = ∫ ω, pathRegret T loss
        (sampledActions play default T (UniformExecution.run κ (context E play loss) T ω)) ∂UniformSeed.law T := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (execution_regret κ E play loss T default)
    _ = _ := by
      rw [← ProbabilityVector.integral_toMeasure]
      have hf : Measurable (fun h : FiniteProcess.History Y T ↦
          pathRegret T loss (sampledActions play default T h)) := Measurable.of_discrete
      exact (UniformExecution.run_hasLaw κ (context E play loss) row hRow T).integral_comp
        hf.aestronglyMeasurable

omit [Fintype ι] [Nonempty ι] [DiscreteMeasurableSpace ι] in
theorem expected_switches_eq_mean
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (E : ι → ι → Prop) (play : (n : ℕ) → Y n → ι)
    (loss : ℕ → ι → ℝ) (T : ℕ) (default : ι)
    (row : (n : ℕ) → FiniteProcess.History Y n → ProbabilityVector (Y n))
    (hRow : ∀ n h, κ n (context E play loss n h)=(row n h).toMeasure) :
    (∫ ω, (switchCount T (fun t ↦ deterministicAction (learner κ play T default) E loss t ω):ℝ)
      ∂UniformSeed.law T)=
      (FiniteProcess.law row T).mean (fun h ↦ (switchCount T (sampledActions play default T h):ℝ)) := by
  calc
    _ = ∫ ω, (switchCount T
        (sampledActions play default T (UniformExecution.run κ (context E play loss) T ω)):ℝ) ∂UniformSeed.law T := by
      apply integral_congr_ae
      filter_upwards [] with ω
      congr 1
      apply switchCount_eq_of_prefix
      intro t ht
      exact execution_action_full κ E play loss T default t ht ω
    _ = _ := by
      rw [← ProbabilityVector.integral_toMeasure]
      have hf : Measurable (fun h : FiniteProcess.History Y T ↦
          (switchCount T (sampledActions play default T h):ℝ)) := Measurable.of_discrete
      exact (UniformExecution.run_hasLaw κ (context E play loss) row hRow T).integral_comp
        hf.aestronglyMeasurable

def strategy
    (κ : (n : ℕ) → Kernel (FiniteProcess.History Y n × Feedback ι n) (Y n))
    [∀ n, IsMarkovKernel (κ n)] (play : (n : ℕ) → Y n → ι) (T : ℕ) (default : ι) : Strategy.{u,0} ι where
  Seed := UniformSeed.Space T
  seedSpace := inferInstance
  law := UniformSeed.law T
  probability := inferInstance
  learner := learner κ play T default

end
end Tournament.Model.MeasurableGame.FiniteFeedback
