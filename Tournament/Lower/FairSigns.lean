module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

@[expose] public section

namespace Tournament.Lower.FairSigns

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators Classical

noncomputable section

def half : unitInterval := ⟨1/2,by constructor <;> norm_num⟩

def coinLaw : Measure Bool := bernoulliMeasure true false half

instance coin_probability : IsProbabilityMeasure coinLaw := by
  unfold coinLaw
  infer_instance

def value : Bool → ℝ | true => 1 | false => -1

theorem value_measurable : Measurable value := Measurable.of_discrete

theorem value_square (b : Bool) : (value b)^2=1 := by cases b <;> norm_num [value]

theorem value_abs (b : Bool) : |value b|=1 := by cases b <;> norm_num [value]

theorem value_integral : ∫ b, value b ∂coinLaw=0 := by
  rw [coinLaw,integral_bernoulliMeasure]
  norm_num [half,value]

abbrev Space (T : ℕ) := Fin T → Bool

def law (T : ℕ) : Measure (Space T) := Measure.pi (fun _ : Fin T ↦ coinLaw)

instance law_probability (T : ℕ) : IsProbabilityMeasure (law T) := by
  unfold law
  infer_instance

def sign {T : ℕ} (t : Fin T) (ω : Space T) : ℝ := value (ω t)

theorem sign_measurable {T : ℕ} (t : Fin T) : Measurable (sign t) :=
  value_measurable.comp (measurable_pi_apply t)

theorem sign_square {T : ℕ} (t : Fin T) (ω : Space T) : (sign t ω)^2=1 := value_square _

theorem signs_independent (T : ℕ) : iIndepFun (sign (T := T)) (law T) :=
  iIndepFun_pi (fun _ ↦ value_measurable.aemeasurable)

theorem sign_law (T : ℕ) (t : Fin T) : HasLaw (sign t) (coinLaw.map value) (law T) := by
  have hvalue : HasLaw value (coinLaw.map value) coinLaw := ⟨value_measurable.aemeasurable,rfl⟩
  exact hvalue.comp (measurePreserving_eval (fun _ : Fin T ↦ coinLaw) t).hasLaw

theorem sign_mean (T : ℕ) (t : Fin T) : ∫ ω, sign t ω ∂law T=0 := by
  calc
    _ = ∫ x : ℝ, x ∂coinLaw.map value := (sign_law T t).integral_eq
    _ = ∫ b, value b ∂coinLaw := integral_map value_measurable.aemeasurable (by fun_prop)
    _ = 0 := value_integral

end
end Tournament.Lower.FairSigns
