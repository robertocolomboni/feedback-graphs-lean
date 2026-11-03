module

public import Tournament.Probability.FiniteConditionalLaw

@[expose] public section

namespace Tournament.FiniteProcess

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

noncomputable section

variable {A C : Type*} [Fintype A] [Fintype C]
variable [MeasurableSpace A] [DiscreteMeasurableSpace A]
variable [MeasurableSpace C] [DiscreteMeasurableSpace C]

theorem product_fresh_hasCondDistrib
    (κ : (n : ℕ) → History (fun _ ↦ A × C) n → ProbabilityVector A) (ν : ProbabilityVector C)
    (n B : ℕ) (h : n+1≤B) :
    let row := fun n s ↦ (κ n s).joint (fun _ ↦ ν)
    HasCondDistrib (fun x ↦ (past (n+1) B h x).2.2)
      (fun x ↦ ((past (n+1) B h x).1,(past (n+1) B h x).2.1))
      (Kernel.const (History (fun _ ↦ A × C) n × A) ν.toMeasure) (law row B).toMeasure := by
  let row := fun n s ↦ (κ n s).joint (fun _ ↦ ν)
  let info := fun x : History (fun _ ↦ A × C) B ↦
    ((past (n+1) B h x).1,(past (n+1) B h x).2.1)
  let source := fun x : History (fun _ ↦ A × C) B ↦ (past (n+1) B h x).2.2
  have hInfo : HasLaw info ((law row n).joint (κ n)).toMeasure (law row B).toMeasure := by
    apply ProbabilityVector.hasLaw_of_mean
    intro f
    calc
      _ = (law row (n+1)).mean (fun s ↦ f (s.1,s.2.1)) := mean_prefix row (n+1) B h _
      _ = ((law row n).joint (κ n)).mean f := by
        rw [law,ProbabilityVector.joint_mean,ProbabilityVector.joint_mean]
        apply congrArg (ProbabilityVector.mean (law row n))
        funext s
        exact ProbabilityVector.joint_first_mean (κ n s) (fun _ ↦ ν) (fun a ↦ f (s,a))
  have hJoint : HasLaw (fun x ↦ (info x,source x))
      (((law row n).joint (κ n)).joint (fun _ ↦ ν)).toMeasure (law row B).toMeasure := by
    apply ProbabilityVector.hasLaw_of_mean
    intro f
    calc
      _ = (law row (n+1)).mean (fun s ↦ f ((s.1,s.2.1),s.2.2)) := mean_prefix row (n+1) B h _
      _ = (((law row n).joint (κ n)).joint (fun _ ↦ ν)).mean f := by
        rw [law,ProbabilityVector.joint_mean,ProbabilityVector.joint_mean,ProbabilityVector.joint_mean]
        apply congrArg (ProbabilityVector.mean (law row n))
        funext s
        exact ProbabilityVector.joint_mean (κ n s) (fun _ ↦ ν) (fun q ↦ f ((s,q.1),q.2))
  change HasLaw (fun x ↦ (info x,source x))
    (((law row B).toMeasure.map info) ⊗ₘ Kernel.const _ ν.toMeasure) (law row B).toMeasure
  rw [hInfo.map_eq]
  change HasLaw _ (((law row n).joint (κ n)).toMeasure ⊗ₘ
    ProbabilityVector.kernel (fun _ ↦ ν) (fun _ ↦ measurable_const)) (law row B).toMeasure
  rw [← ProbabilityVector.toMeasure_joint]
  exact hJoint

end
end Tournament.FiniteProcess
