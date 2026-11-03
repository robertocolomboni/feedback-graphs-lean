module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Data.EReal.Operations

@[expose] public section

namespace Tournament.ExtendedExpectation

open scoped BigOperators MeasureTheory ENNReal Classical
open MeasureTheory Filter

noncomputable section

variable {Ω α : Type*} [MeasurableSpace Ω]

def mean (μ : Measure Ω) (a : ℝ) (f : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (f ω+a) ∂μ):EReal)-(a:EReal)

theorem mean_ne_bot (μ : Measure Ω) (a : ℝ) (f : Ω → ℝ) : mean μ a f≠⊥ := by
  unfold mean
  rw [sub_eq_add_neg,EReal.add_ne_bot_iff]
  exact ⟨EReal.coe_ennreal_ne_bot _,by simp⟩

theorem mean_of_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (f : Ω → ℝ)
    (hf : Integrable f μ) (ha : ∀ᵐ ω ∂μ, 0≤f ω+a) : mean μ a f=(∫ ω, f ω ∂μ:ℝ) := by
  have hshift : Integrable (fun ω ↦ f ω+a) μ := hf.add (integrable_const a)
  have hnonneg : 0≤∫ ω, (f ω+a) ∂μ := integral_nonneg_of_ae ha
  have hvalue : (∫ ω, (f ω+a) ∂μ)=(∫ ω, f ω ∂μ)+a := by
    rw [integral_add hf (integrable_const a)]
    simp
  unfold mean
  rw [← ofReal_integral_eq_lintegral_ofReal hshift ha,EReal.coe_ennreal_ofReal,max_eq_left hnonneg,
    ← EReal.coe_sub,hvalue]
  congr 1
  ring

theorem mean_eq_top_of_not_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (ha : ∀ᵐ ω ∂μ, 0≤f ω+a) (hfi : ¬Integrable f μ) :
    mean μ a f=⊤ := by
  have hlin : (∫⁻ ω, ENNReal.ofReal (f ω+a) ∂μ)=∞ := by
    by_contra hne
    have hfinite : HasFiniteIntegral (fun ω ↦ f ω+a) μ :=
      (hasFiniteIntegral_iff_ofReal ha).mpr (lt_top_iff_ne_top.mpr hne)
    have hshift : Integrable (fun ω ↦ f ω+a) μ := ⟨hf.fun_add aestronglyMeasurable_const,hfinite⟩
    have hsub : Integrable (fun ω ↦ (f ω+a)-a) μ := hshift.sub (integrable_const a)
    apply hfi
    exact hsub.congr (Eventually.of_forall (fun _ ↦ by ring))
  simp [mean,hlin]

theorem mean_shift_independent (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℝ) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (ha : ∀ᵐ ω ∂μ, 0≤f ω+a) (hb : ∀ᵐ ω ∂μ, 0≤f ω+b) :
    mean μ a f=mean μ b f := by
  by_cases hfi : Integrable f μ
  · rw [mean_of_integrable μ a f hfi ha,mean_of_integrable μ b f hfi hb]
  · rw [mean_eq_top_of_not_integrable μ a f hf ha hfi,mean_eq_top_of_not_integrable μ b f hf hb hfi]

theorem coe_finsetSum (s : Finset α) (f : α → ℝ) : (((∑ a ∈ s, f a):ℝ):EReal)=∑ a ∈ s, (f a:EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha,EReal.coe_add,ih]

theorem finsetSum_ne_bot (s : Finset α) (f : α → EReal) (hf : ∀ a ∈ s, f a≠⊥) : (∑ a ∈ s, f a)≠⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,EReal.add_ne_bot_iff]
    exact ⟨hf a (Finset.mem_insert_self _ _),ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))⟩

theorem finsetSum_eq_top_of_mem (s : Finset α) (f : α → EReal) (hf : ∀ a ∈ s, f a≠⊥)
    (htop : ∃ a ∈ s, f a=⊤) : (∑ a ∈ s, f a)=⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at htop
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hfa : f a=⊤
    · rw [hfa]
      exact EReal.top_add_of_ne_bot (finsetSum_ne_bot s f (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))
    · obtain ⟨b,hb,hbtop⟩ := htop
      have hb' : b∈s := by
        rcases Finset.mem_insert.mp hb with hba | hb
        · exact False.elim (hfa (hba ▸ hbtop))
        · exact hb
      rw [ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)) ⟨b,hb',hbtop⟩]
      exact EReal.add_top_of_ne_bot (hf a (Finset.mem_insert_self _ _))

end
end Tournament.ExtendedExpectation
