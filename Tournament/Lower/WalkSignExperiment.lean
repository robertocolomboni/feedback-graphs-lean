module

public import Tournament.Lower.GaussianWalkIndependence
public import Tournament.Lower.FairSigns

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

noncomputable section

theorem hasLaw_constant_sections {Z Ω X : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace X] (ν : Measure Z) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [SFinite μ] (κ : Measure X) (f : Z × Ω → X) (hf : Measurable f)
    (hsection : ∀ z, HasLaw (fun ω ↦ f (z,ω)) κ μ) : HasLaw f κ (ν.prod μ) where
  aemeasurable := hf.aemeasurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply hf hs,Measure.prod_apply (hf hs)]
    calc
      _ = ∫⁻ _z, κ s ∂ν := by
        apply lintegral_congr
        intro z
        change μ {ω | f (z,ω)∈s}=κ s
        exact (hsection z).measure_eq hs
      _ = _ := by simp

namespace WalkSign

abbrev Space (T : ℕ) (C : Type*) := FairSigns.Space T × GaussianProduct.Space T C

variable {C : Type*} [Fintype C]

def law (T : ℕ) (v : ℝ≥0) : Measure (Space T C) :=
  (FairSigns.law T).prod (GaussianProduct.law T v)

instance law_probability (T : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (law (C := C) T v) := by
  unfold law
  infer_instance

def walk {T : ℕ} (c : C) (t : ℕ) (ω : Space T C) : ℝ := GaussianProduct.walk c t ω.2

def sign {T : ℕ} (t : Fin T) (ω : Space T C) : ℝ := FairSigns.sign t ω.1

omit [Fintype C] in
theorem walk_measurable (T : ℕ) (c : C) (t : ℕ) : Measurable (walk (T := T) c t) :=
  (GaussianProduct.walk_measurable T c t).comp measurable_snd

omit [Fintype C] in
theorem sign_measurable (T : ℕ) (t : Fin T) : Measurable (sign (T := T) (C := C) t) :=
  (FairSigns.sign_measurable t).comp measurable_fst

omit [Fintype C] in
theorem sign_square {T : ℕ} (t : Fin T) (ω : Space T C) : (sign t ω)^2=1 :=
  FairSigns.sign_square t ω.1

def gaussianPart {T : ℕ} (c d : C) (t : Fin T) (ω : Space T C) : ℝ :=
  walk c (t.val+1) ω+sign t ω*walk d (t.val+1) ω

omit [Fintype C] in
theorem gaussianPart_measurable (T : ℕ) (c d : C) (t : Fin T) :
    Measurable (gaussianPart c d t) :=
  (walk_measurable T c _).add ((sign_measurable T t).mul (walk_measurable T d _))

theorem gaussianPart_law (T : ℕ) (v : ℝ≥0) (c d : C) (hcd : c≠d) (t : Fin T) :
    HasLaw (gaussianPart c d t)
      (gaussianReal 0 (2*((Dyadic.incrementSet T (t.val+1)).card • v))) (law T v) := by
  apply hasLaw_constant_sections (FairSigns.law T) (GaussianProduct.law T v) _
    (gaussianPart c d t) (gaussianPart_measurable T c d t)
  intro z
  exact GaussianProduct.common_signed_walk_law T v c d hcd _ (FairSigns.sign t z)
    (FairSigns.sign_square t z)

theorem walk_law (T : ℕ) (v : ℝ≥0) (c : C) (t : ℕ) :
    HasLaw (walk c t) (gaussianReal 0 ((Dyadic.incrementSet T t).card • v)) (law T v) := by
  exact (GaussianProduct.walk_law T v c t).comp measurePreserving_snd.hasLaw

theorem sign_mean (T : ℕ) (v : ℝ≥0) (t : Fin T) :
    ∫ ω, sign (C := C) t ω ∂law T v=0 := by
  have h := (FairSigns.sign_law T t).comp
    (measurePreserving_fst (μ := FairSigns.law T) (ν := GaussianProduct.law (C := C) T v)).hasLaw
  have h' : HasLaw (sign (C := C) t) (FairSigns.coinLaw.map FairSigns.value) (law T v) := h
  rw [h'.integral_eq]
  rw [← (FairSigns.sign_law T t).integral_eq]
  exact FairSigns.sign_mean T t

end WalkSign
end
end Tournament.Lower
