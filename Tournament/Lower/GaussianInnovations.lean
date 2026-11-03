module

public import Tournament.Lower.WalkSignExperiment
public import Tournament.Lower.GaussianConditional
public import Tournament.Probability.PrivateIndependence

@[expose] public section

namespace Tournament.Lower.GaussianProduct

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

variable {C : Type*} [Fintype C]

def currentIndices {T : ℕ} (t : Fin T) : Finset (Fin T × C) := Finset.univ.filter (fun p ↦ p.1=t)

def otherIndices {T : ℕ} (t : Fin T) : Finset (Fin T × C) := Finset.univ.filter (fun p ↦ p.1≠t)

def currentSnapshot {T : ℕ} (t : Fin T) (ω : Space T C) : C → ℝ := fun c ↦ ω (t,c)

def otherSnapshot {T : ℕ} (t : Fin T) (ω : Space T C) : otherIndices (C := C) t → ℝ := fun p ↦ ω p

def restoreOther {T : ℕ} (t : Fin T) (x : otherIndices (C := C) t → ℝ) : Space T C :=
  fun p ↦ if hp : p∈otherIndices t then x ⟨p,hp⟩ else 0

def eraseRow {T : ℕ} (t : Fin T) (ω : Space T C) : Space T C := fun p ↦ if p.1=t then 0 else ω p

omit [Fintype C] in
theorem currentSnapshot_measurable {T : ℕ} (t : Fin T) : Measurable (currentSnapshot (C := C) t) :=
  Measurable.of_eval (fun c ↦ measurable_pi_apply (t,c))

theorem otherSnapshot_measurable {T : ℕ} (t : Fin T) : Measurable (otherSnapshot (C := C) t) :=
  Measurable.of_eval (fun p ↦ measurable_pi_apply p.val)

theorem restoreOther_measurable {T : ℕ} (t : Fin T) : Measurable (restoreOther (C := C) t) := by
  apply Measurable.of_eval
  intro p
  by_cases hp : p∈otherIndices (C := C) t
  · simp only [restoreOther,dite_eq_left hp]
    exact measurable_pi_apply (⟨p,hp⟩ : otherIndices (C := C) t)
  · simp only [restoreOther,dite_eq_right hp]
    exact measurable_const

theorem restoreOther_snapshot {T : ℕ} (t : Fin T) (ω : Space T C) :
    restoreOther t (otherSnapshot t ω)=eraseRow t ω := by
  funext p
  by_cases hp : p.1=t <;> simp [restoreOther,otherIndices,otherSnapshot,eraseRow,hp]

theorem current_other_disjoint {T : ℕ} (t : Fin T) :
    Disjoint (otherIndices (C := C) t) (currentIndices (C := C) t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2

theorem currentSnapshot_law (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    HasLaw (currentSnapshot (C := C) t) (GaussianKL.productLaw (0 : C → ℝ) v) (law T v) := by
  have hi : iIndepFun (fun c : C ↦ fun ω : Space T C ↦ ω (t,c)) (law T v) :=
    iIndepFun.precomp (g := fun c : C ↦ (t,c)) (fun _ _ h ↦ congrArg Prod.snd h)
      (all_increments_independent T v)
  have hLaw (c : C) : HasLaw (fun ω : Space T C ↦ ω (t,c)) (gaussianReal 0 v) (law T v) :=
    (measurePreserving_eval (fun _ : Fin T × C ↦ gaussianReal 0 v) (t,c)).hasLaw
  exact hi.hasLaw_pi hLaw

theorem current_other_independent (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    IndepFun (otherSnapshot (C := C) t) (currentSnapshot t) (law T v) := by
  have hi := iIndepFun.indepFun_finset (otherIndices (C := C) t) (currentIndices t)
    (current_other_disjoint t) (all_increments_independent T v) (fun p ↦ measurable_pi_apply p)
  have heval : Measurable (fun y : currentIndices (C := C) t → ℝ ↦ fun c : C ↦
      y ⟨(t,c),by simp [currentIndices]⟩) :=
    Measurable.of_eval (fun c ↦ measurable_pi_apply
      (⟨(t,c),by simp [currentIndices]⟩ : currentIndices (C := C) t))
  exact hi.comp (φ := id) (ψ := fun y : currentIndices (C := C) t → ℝ ↦ fun c : C ↦
    y ⟨(t,c),by simp [currentIndices]⟩) measurable_id heval

variable {Seed : Type*} [MeasurableSpace Seed]

theorem current_independent_private (ν : Measure Seed) [IsProbabilityMeasure ν]
    (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    IndepFun (fun p : Seed × WalkSign.Space T C ↦ (p.1,(p.2.1,otherSnapshot t p.2.2)))
      (fun p ↦ currentSnapshot t p.2.2) (ν.prod (WalkSign.law T v)) := by
  have hi := Tournament.Probability.independent_private_extension (law (C := C) T v) (FairSigns.law T)
    (otherSnapshot t) (currentSnapshot t) (otherSnapshot_measurable t) (currentSnapshot_measurable t)
    (current_other_independent T v t)
  exact Tournament.Probability.independent_private_extension (WalkSign.law (C := C) T v) ν
    (fun p ↦ (p.1,otherSnapshot t p.2)) (fun p ↦ currentSnapshot t p.2)
    (measurable_fst.prodMk ((otherSnapshot_measurable t).comp measurable_snd))
    ((currentSnapshot_measurable t).comp measurable_snd) hi

theorem currentSnapshot_private_law (ν : Measure Seed) [IsProbabilityMeasure ν]
    (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    HasLaw (fun p : Seed × WalkSign.Space T C ↦ currentSnapshot t p.2.2)
      (GaussianKL.productLaw (0 : C → ℝ) v) (ν.prod (WalkSign.law T v)) := by
  have hwalk : HasLaw (fun p : WalkSign.Space T C ↦ currentSnapshot t p.2)
      (GaussianKL.productLaw (0 : C → ℝ) v) (WalkSign.law T v) :=
    (currentSnapshot_law T v t).comp (measurePreserving_snd (μ := FairSigns.law T) (ν := law T v)).hasLaw
  exact hwalk.comp (measurePreserving_snd (μ := ν) (ν := WalkSign.law T v)).hasLaw

end
end Tournament.Lower.GaussianProduct
