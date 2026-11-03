module

public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem setBernoulli_inter (U A : Set ι) (p : unitInterval) :
    (setBernoulli U p).map (fun S ↦ S∩A)=setBernoulli (U∩A) p := by
  let μ := fun i : ι ↦ bernoulliMeasure (i∈U) False p
  let ξ := fun i : ι ↦ bernoulliMeasure (i∈U∩A) False p
  let mask : (ι → Prop) → ι → Prop := fun b i ↦ b i ∧ i∈A
  let toSet : (ι → Prop) → Set ι := fun b ↦ {i | b i}
  have hMarg (i : ι) : (μ i).map (fun b : Prop ↦ b ∧ i∈A)=ξ i := by
    rw [map_bernoulliMeasure]
    simp only [ξ,Set.mem_inter_iff,false_and]
  have hMask : (Measure.infinitePi μ).map mask=Measure.infinitePi ξ := by
    calc
      _ = Measure.infinitePi (fun i ↦ (μ i).map (fun b : Prop ↦ b ∧ i∈A)) :=
        Measure.infinitePi_map_pi μ (fun _ ↦ measurable_of_finite _)
      _ = _ := by congr 1; funext i; exact hMarg i
  calc
    _ = (Measure.infinitePi μ).map (fun b ↦ toSet b∩A) := by
      rw [setBernoulli_eq_map,Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    _ = ((Measure.infinitePi μ).map mask).map toSet := by
      rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    _ = (Measure.infinitePi ξ).map toSet := by rw [hMask]
    _ = _ := (setBernoulli_eq_map (U∩A) p).symm

theorem intersection_count_law (U A : Set ι) (p : unitInterval) :
    HasLaw (fun S : Set ι ↦ (S∩A).ncard) ((setBernoulli (U∩A) p).map Set.ncard) (setBernoulli U p) := by
  refine ⟨(measurable_of_finite _).aemeasurable,?_⟩
  rw [← setBernoulli_inter U A p,Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem intersection_count_probability (U A : Set ι) (p : unitInterval) (b : ℕ) :
    (setBernoulli U p).real {S | (S∩A).ncard=b}=
      ((U∩A).ncard.choose b:ℝ)*(p:ℝ)^b*(1-(p:ℝ))^((U∩A).ncard-b) := by
  have h := intersection_count_law U A p
  calc
    _ = ((setBernoulli (U∩A) p).map Set.ncard).real {b} :=
      h.measureReal_eq (p := fun n ↦ n=b) (measurableSet_singleton b)
    _ = _ := map_ncard_setBernoulli_real_singleton (Set.toFinite (U∩A)) p b

end
end Tournament.Probability
