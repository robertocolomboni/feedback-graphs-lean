module

public import Tournament.Lower.GaussianProductKL
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

variable {C : Type*} [Fintype C]

theorem productLaw_map_const_add (m shift : C → ℝ) (v : ℝ≥0) :
    (productLaw m v).map (fun x ↦ shift+x)=productLaw (shift+m) v := by
  let (c : C) : SigmaFinite ((gaussianReal (m c) v).map (fun x ↦ shift c+x)) := by
    rw [gaussianReal_map_const_add]
    infer_instance
  change (Measure.pi (fun c ↦ gaussianReal (m c) v)).map (fun x c ↦ shift c+x c)=_
  rw [Measure.pi_map_pi (f := fun c (x : ℝ) ↦ shift c+x)
    (fun _ ↦ (measurable_const.add measurable_id).aemeasurable)]
  unfold productLaw
  congr 1
  funext c
  calc
    _ = gaussianReal (m c+shift c) v := gaussianReal_map_const_add (shift c)
    _ = _ := by rw [add_comm]; rfl

variable {A : Type*} [MeasurableSpace A]

theorem density_joint_measurable (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) :
    Measurable (fun p : A × (C → ℝ) ↦ density (m p.1) v p.2) := by
  apply Finset.measurable_prod
  intro c _
  have hc := (measurable_pi_apply c).comp hm
  exact measurable_uncurry_gaussianPDF.comp
    ((hc.comp measurable_fst).prodMk (measurable_const.prodMk ((measurable_pi_apply c).comp measurable_snd)))

def gaussianKernel (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) : Kernel A (C → ℝ) where
  toFun a := productLaw (m a) v
  measurable' := by
    have heq : (fun a ↦ productLaw (m a) v)=(fun a ↦ (base C).withDensity (density (m a) v)) := by
      funext a
      exact productLaw_eq_withDensity (m a) v hv
    rw [heq]
    exact measurable_withDensity (density_joint_measurable m hm v)

instance gaussianKernel_markov (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) :
    IsMarkovKernel (gaussianKernel m hm v hv) where
  isProbabilityMeasure a := productLaw_probability (m a) v

theorem gaussianKernel_apply (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) (a : A) :
    gaussianKernel m hm v hv a=productLaw (m a) v := rfl

theorem shifted_product_eq_compProd (ν : Measure A) [SFinite ν] (m : A → C → ℝ) (hm : Measurable m)
    (v : ℝ≥0) (hv : v≠0) :
    (ν.prod (productLaw (0 : C → ℝ) v)).map (fun p ↦ (p.1,m p.1+p.2))=
      ν ⊗ₘ gaussianKernel m hm v hv := by
  have hmap : Measurable (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) :=
    measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd)
  ext s hs
  rw [Measure.map_apply hmap hs,Measure.prod_apply (hmap hs),Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  have hshift : (productLaw (0 : C → ℝ) v).map (fun x ↦ m a+x)=productLaw (m a) v := by
    simpa only [add_zero] using productLaw_map_const_add (0 : C → ℝ) (m a) v
  rw [gaussianKernel_apply,← hshift,
    Measure.map_apply (f := fun x : C → ℝ ↦ m a+x) (measurable_const.add measurable_id) (measurable_prodMk_left hs)]
  rfl

theorem hasCondDistrib_shifted_innovation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → A) (hX : Measurable X) (Z : Ω → C → ℝ)
    (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0)
    (hZ : HasLaw Z (productLaw (0 : C → ℝ) v) μ) (hIndep : IndepFun X Z μ) :
    HasCondDistrib (fun ω ↦ m (X ω)+Z ω) X (gaussianKernel m hm v hv) μ := by
  have hLawX : HasLaw X (μ.map X) μ := ⟨hX.aemeasurable,rfl⟩
  have hpair := hIndep.hasLaw_prod hLawX hZ
  have hmap : Measurable (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) :=
    measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd)
  refine ⟨hX.aemeasurable.prodMk ((hm.comp hX).aemeasurable.add hZ.aemeasurable),?_⟩
  calc
    _ = (μ.map (fun ω ↦ (X ω,Z ω))).map (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) := by
      rw [AEMeasurable.map_map_of_aemeasurable hmap.aemeasurable hpair.aemeasurable]
      rfl
    _ = ((μ.map X).prod (productLaw (0 : C → ℝ) v)).map
        (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) := by rw [hpair.map_eq]
    _ = _ := shifted_product_eq_compProd (μ.map X) m hm v hv

end
end Tournament.Lower.GaussianKL
