module

public import Tournament.Probability.UniformSeed

@[expose] public section

namespace Tournament.Probability.UniformExecution

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval
noncomputable section

universe u v
variable {X : ℕ → Type v} {Y : ℕ → Type u}
variable [∀ n, MeasurableSpace (X n)]
variable [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
variable [∀ n, MeasurableSpace (Y n)] [∀ n, StandardBorelSpace (Y n)]
variable [∀ n, DiscreteMeasurableSpace (Y n)]

omit [∀ n, MeasurableSpace (X n)]
  [∀ n, Nonempty (Y n)] [∀ n, StandardBorelSpace (Y n)] in
theorem history_succ_space (n : ℕ) :
    @Prod.instMeasurableSpace (FiniteProcess.History Y n) (Y n)
      (FiniteProcess.historyMeasurableSpace n) (inferInstance)=FiniteProcess.historyMeasurableSpace (n+1) := by
  apply top_unique
  intro s _
  exact MeasurableSet.of_discrete

def run (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n) :
    (n : ℕ) → UniformSeed.Space n → FiniteProcess.History Y n
  | 0, _ => ULift.up ()
  | n+1, ω =>
      let h := run κ c n (Fin.init ω)
      (h,KernelSampler.draw (κ n) (c n h) (ω (Fin.last n)))

theorem run_measurable (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n) (n : ℕ) : Measurable (run κ c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hInit : Measurable (fun ω : UniformSeed.Space (n+1) ↦ Fin.init ω) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    have hPast : Measurable (fun ω : UniformSeed.Space (n+1) ↦ run κ c n (Fin.init ω)) := ih.comp hInit
    have hContext : Measurable (fun ω : UniformSeed.Space (n+1) ↦ c n (run κ c n (Fin.init ω))) :=
      (Measurable.of_discrete (f := c n)).comp
        (f := fun ω : UniformSeed.Space (n+1) ↦ run κ c n (Fin.init ω)) hPast
    rw [← history_succ_space (Y := Y) n]
    exact hPast.prodMk (KernelSampler.draw_measurable_comp (κ n)
      (fun ω : UniformSeed.Space (n+1) ↦ c n (run κ c n (Fin.init ω)))
      (fun ω : UniformSeed.Space (n+1) ↦ ω (Fin.last n)) hContext (measurable_pi_apply _))

theorem run_hasLaw (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n)
    (row : (n : ℕ) → FiniteProcess.History Y n → ProbabilityVector (Y n))
    (hRow : ∀ n h, κ n (c n h)=(row n h).toMeasure) (n : ℕ) :
    HasLaw (run κ c n) (FiniteProcess.law row n).toMeasure (UniformSeed.law n) := by
  induction n with
  | zero =>
    refine ⟨measurable_const.aemeasurable,?_⟩
    apply Measure.ext_of_singleton
    rintro ⟨⟨⟩⟩
    simp [run,Measure.map_const,ProbabilityVector.toMeasure_singleton,FiniteProcess.law,
      FiniteProcess.initial]
  | succ n ih =>
    have hLaw := (KernelSampler.extend_finite_hasLaw (UniformSeed.law n) (run κ c n)
      (run_measurable κ c n) (FiniteProcess.law row n) ih (κ n) (c n) (row n) (hRow n)).comp
        (UniformSeed.prefix_fresh_hasLaw n)
    rw [← history_succ_space (Y := Y) n]
    exact hLaw

def runPrefix (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n) (n B : ℕ) (h : n≤B)
    (ω : UniformSeed.Space B) : FiniteProcess.History Y n := run κ c n (UniformSeed.take n B h ω)

theorem runPrefix_hasLaw (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n)
    (row : (n : ℕ) → FiniteProcess.History Y n → ProbabilityVector (Y n))
    (hRow : ∀ n h, κ n (c n h)=(row n h).toMeasure) (n B : ℕ) (h : n≤B) :
    HasLaw (runPrefix κ c n B h) (FiniteProcess.law row n).toMeasure (UniformSeed.law B) :=
  (run_hasLaw κ c row hRow n).comp (UniformSeed.take_hasLaw n B h)

omit [∀ n, Fintype (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)] in
theorem runPrefix_past (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n)
    (a b B : ℕ) (hab : a≤b) (hbB : b≤B) (ω : UniformSeed.Space B) :
    FiniteProcess.past a b hab (runPrefix κ c b B hbB ω)=runPrefix κ c a B (hab.trans hbB) ω := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    simp [FiniteProcess.past_self]
  | succ b ih =>
    by_cases ha : a=b+1
    · subst a
      exact FiniteProcess.past_self _ _
    · have hab' : a≤b := by omega
      rw [FiniteProcess.past_succ a b hab']
      change FiniteProcess.past a b hab' (run κ c b (Fin.init (UniformSeed.take (b+1) B hbB ω)))=_
      rw [UniformSeed.take_init]
      exact ih hab' (by omega)

omit [∀ n, Fintype (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)] in
theorem run_past (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (c : (n : ℕ) → FiniteProcess.History Y n → X n)
    (a B : ℕ) (h : a≤B) (ω : UniformSeed.Space B) :
    FiniteProcess.past a B h (run κ c B ω)=runPrefix κ c a B h ω := by
  simpa only [runPrefix,UniformSeed.take_self] using runPrefix_past κ c a B B h le_rfl ω

end
end Tournament.Probability.UniformExecution
