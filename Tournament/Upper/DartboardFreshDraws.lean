module

public import Tournament.Upper.DartboardGuarantee
public import Tournament.Probability.StoppedChunkCoupling

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def freshDrawLaw (p : ProbabilityVector ι) (η : ℝ) (hη : 0≤η)
    (g : ι → ℝ) (hg : ∀ i, 0≤g i) (i : ι) : ProbabilityVector (Bool × ι) :=
  (Restarts.coin (keep η g i) (keep_pos η g i).le (keep_le_one η hη g hg i)).joint
    (fun _ ↦ Model.exponentialUpdate p η g)

theorem row_mean (p : ProbabilityVector ι) (η : ℝ) (hη : 0≤η)
    (g : ι → ℝ) (hg : ∀ i, 0≤g i) (i : ι) (f : ι → ℝ) :
    ((kernel p η hη g hg).row i).mean f=
      keep η g i*f i+(1-keep η g i)*(Model.exponentialUpdate p η g).mean f := by
  change (∑ j, ((if i=j then keep η g i else 0)+
    (1-keep η g i)*Model.exponentialUpdate p η g j)*f j)=_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hFirst : (∑ j, (if i=j then keep η g i else 0)*f j)=keep η g i*f i := by
    simp only [ite_mul,zero_mul]
    simp
  rw [hFirst]
  congr 1
  simp only [ProbabilityVector.mean,mul_assoc,Finset.mul_sum]

theorem freshDrawLaw_mean (p : ProbabilityVector ι) (η : ℝ) (hη : 0≤η)
    (g : ι → ℝ) (hg : ∀ i, 0≤g i) (i : ι) (f : ι → ℝ) :
    (freshDrawLaw p η hη g hg i).mean (fun q ↦ f (if q.1 then i else q.2))=
      ((kernel p η hη g hg).row i).mean f := by
  rw [freshDrawLaw,ProbabilityVector.joint_mean,Restarts.coin_mean,row_mean]
  simp only [ite_true,Bool.false_eq_true,ite_false,ProbabilityVector.mean_const]

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem freshDrawLaw_map (p : ProbabilityVector ι) (η : ℝ) (hη : 0≤η)
    (g : ι → ℝ) (hg : ∀ i, 0≤g i) (i : ι) :
    (freshDrawLaw p η hη g hg i).toMeasure.map (fun q ↦ if q.1 then i else q.2)=
      ((kernel p η hη g hg).row i).toMeasure := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro j
  rw [← integral_indicator_one (measurableSet_singleton j),
    ← integral_indicator_one (measurableSet_singleton j),
    integral_map (Measurable.of_discrete).aemeasurable (Measurable.of_discrete).aestronglyMeasurable,
    ProbabilityVector.integral_toMeasure,ProbabilityVector.integral_toMeasure]
  exact freshDrawLaw_mean p η hη g hg i _

end
end Tournament.Upper.ShrinkingDartboard
