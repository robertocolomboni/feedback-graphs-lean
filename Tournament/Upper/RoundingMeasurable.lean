module

public import Tournament.Upper.RoundedPreparation
public import Tournament.Probability.MeasurableFactor
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

namespace Tournament.Upper.Rounding

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

def code (w : ProbabilityVector ι) (T : ℕ) : ι → ℕ := fun i ↦ numerator w T i

theorem code_measurable (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ) :
    Measurable (fun a ↦ code (p a) T) :=
  Measurable.of_eval (fun i ↦ (measurable_const.mul (hp i)).nat_ceil)

omit [MeasurableSpace A] in
theorem anchor_eq_of_code_eq (p q : ProbabilityVector ι) (T : ℕ) (hT : 0<T)
    (hCode : code p T=code q T) : anchor p T hT=anchor q T hT := by
  have hNum (i : ι) : numerator p T i=numerator q T i := congrFun hCode i
  have hDen : denominator p T=denominator q T := by simp only [denominator,hNum]
  apply ProbabilityVector.ext_weights
  intro i
  change (numerator p T i:ℝ)/(denominator p T:ℝ)=(numerator q T i:ℝ)/(denominator q T:ℝ)
  rw [hNum,hDen]

theorem rounded_functional_measurable (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ) (hT : 0<T)
    (hPos : ∀ a i, 0<anchor (p a) T hT i)
    (f : {v : ProbabilityVector ι // ∀ i, 0<v i} → ℝ) :
    Measurable (fun a ↦ f ⟨anchor (p a) T hT,hPos a⟩) := by
  apply Probability.measurable_of_discrete_factor (fun a ↦ code (p a) T) (code_measurable p hp T)
  intro a b hCode
  apply congrArg f
  exact Subtype.ext (anchor_eq_of_code_eq (p a) (p b) T hT hCode)

theorem optimized_matrix_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ) (hT : 0<T)
    (hPos : ∀ a i, 0<anchor (p a) T hT i) (s i r : ι) :
    Measurable (fun a ↦ (optimizedAssignment F hF (anchor (p a) T hT) (hPos a)).matrix s i r) :=
  rounded_functional_measurable p hp T hT hPos (fun v ↦ (optimizedAssignment F hF v.1 v.2).matrix s i r)

theorem optimized_source_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ) (hT : 0<T)
    (hPos : ∀ a i, 0<anchor (p a) T hT i) (s : ι) :
    Measurable (fun a ↦ (optimizedAssignment F hF (anchor (p a) T hT) (hPos a)).sourceWeight s) :=
  rounded_functional_measurable p hp T hT hPos (fun v ↦ (optimizedAssignment F hF v.1 v.2).sourceWeight s)

theorem optimized_sourceLaw_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ) (hT : 0<T)
    (hPos : ∀ a i, 0<anchor (p a) T hT i) (s : ι) :
    Measurable (fun a ↦ (optimizedAssignment F hF (anchor (p a) T hT) (hPos a)).sourceLaw s) :=
  rounded_functional_measurable p hp T hT hPos (fun v ↦ (optimizedAssignment F hF v.1 v.2).sourceLaw s)

end
end Tournament.Upper.Rounding
