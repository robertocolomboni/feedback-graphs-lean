module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace Tournament.Probability.BernoulliCoins

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators unitInterval
noncomputable section

def coinLaw (p : unitInterval) : Measure Bool := bernoulliMeasure true false p

instance coinLaw_probability (p : unitInterval) : IsProbabilityMeasure (coinLaw p) := by
  unfold coinLaw
  infer_instance

def productLaw (ι : Type*) [Fintype ι] (p : unitInterval) : Measure (ι → Bool) :=
  Measure.pi (fun _ : ι ↦ coinLaw p)

instance productLaw_probability (ι : Type*) [Fintype ι] (p : unitInterval) :
    IsProbabilityMeasure (productLaw ι p) := by unfold productLaw; infer_instance

variable {ι : Type*} [Fintype ι]

theorem coin_true_real (p : unitInterval) : (coinLaw p).real {true}=(p:ℝ) := by
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton true) rfl (by decide)

theorem coin_false_real (p : unitInterval) : (coinLaw p).real {false}=1-(p:ℝ) := by
  exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton false) (by decide) rfl

theorem coordinate_true_probability (p : unitInterval) (i : ι) :
    (productLaw ι p).real {ω | ω i=true}=(p:ℝ) := by
  have h := (measurePreserving_eval (fun _ : ι ↦ coinLaw p) i).hasLaw
  calc
    _ = (coinLaw p).real {true} := h.measureReal_eq (p := fun b ↦ b=true) (measurableSet_singleton true)
    _ = _ := coin_true_real p

theorem avoid_probability (p : unitInterval) (A : Finset ι) :
    (productLaw ι p).real {ω | ∀ i∈A, ω i=false}=(1-(p:ℝ))^A.card := by
  have hSet : {ω : ι → Bool | ∀ i∈A, ω i=false}=(A : Set ι).pi (fun _ ↦ {false}) := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff]
  unfold Measure.real productLaw
  rw [hSet,Measure.pi_pi_finset]
  rw [Finset.prod_const,ENNReal.toReal_pow]
  change ((coinLaw p).real {false})^A.card=_
  rw [coin_false_real]

theorem independent_of_coordinate [DecidableEq ι] {β : Type*} [MeasurableSpace β]
    (p : unitInterval) (i : ι) (F : (ι → Bool) → β)
    (hReset : ∀ ω, F (Function.update ω i false)=F ω) :
    IndepFun F (fun ω ↦ ω i) (productLaw ι p) := by
  let S : Finset ι := Finset.univ.erase i
  let fill : (S → Bool) → ι → Bool := fun b j ↦ if hj : j∈S then b ⟨j,hj⟩ else false
  let f : (S → Bool) → β := fun b ↦ F (fill b)
  let g : (({i}:Finset ι) → Bool) → Bool := fun b ↦ b ⟨i,by simp⟩
  have hI : iIndepFun (fun j (ω : ι → Bool) ↦ ω j) (productLaw ι p) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hDisjoint : Disjoint S ({i}:Finset ι) := by simp [S]
  have hGroups := hI.indepFun_finset S {i} hDisjoint (fun _ ↦ measurable_pi_apply _)
  have hComp := hGroups.comp (Measurable.of_discrete (f := f)) (Measurable.of_discrete (f := g))
  have hFill (ω : ι → Bool) : fill (fun j : S ↦ ω j)=Function.update ω i false := by
    funext j
    by_cases hj : j=i <;> simp [fill,S,hj]
  have hF : (fun ω : ι → Bool ↦ f (fun j : S ↦ ω j))=F := by
    funext ω
    exact (congrArg F (hFill ω)).trans (hReset ω)
  change IndepFun (fun ω : ι → Bool ↦ f (fun j : S ↦ ω j)) (fun ω ↦ ω i) (productLaw ι p) at hComp
  rw [hF] at hComp
  exact hComp

theorem fresh_success_probability [DecidableEq ι] (p : unitInterval) (i : ι) (F : (ι → Bool) → Bool)
    (hReset : ∀ ω, F (Function.update ω i false)=F ω) :
    (productLaw ι p).real {ω | F ω=true ∧ ω i=true}=
      (productLaw ι p).real {ω | F ω=true}*(p:ℝ) := by
  have h := (independent_of_coordinate p i F hReset).measure_inter_preimage_eq_mul
    {true} {true} (measurableSet_singleton true) (measurableSet_singleton true)
  have hReal := congrArg ENNReal.toReal h
  have hFPre : F ⁻¹' {true}={ω | F ω=true} := by ext ω; simp
  have hCPre : (fun ω : ι → Bool ↦ ω i) ⁻¹' {true}={ω | ω i=true} := by ext ω; simp
  rw [hFPre,hCPre] at hReal
  have hProduct : (productLaw ι p).real {ω | F ω=true ∧ ω i=true}=
      (productLaw ι p).real {ω | F ω=true}*(productLaw ι p).real {ω | ω i=true} := by
    simpa only [ENNReal.toReal_mul,← measureReal_def,Set.ofPred_and] using hReal
  rw [hProduct,coordinate_true_probability]

end
end Tournament.Probability.BernoulliCoins
