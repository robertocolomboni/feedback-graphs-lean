module

public import Tournament.Probability.CompactOptimization
public import Tournament.Probability.MeasurableSelection

@[expose] public section

namespace Tournament.Probability.CompactOptimization

open Set TopologicalSpace
open scoped Classical

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X]
variable [MetricSpace Y] [CompactSpace Y] [SeparableSpace Y] [Nonempty Y]
variable [MeasurableSpace Y] [BorelSpace Y]

theorem exists_measurable_optimizer_below_sentinel
    (R : X → Y → Prop) (f : Y → ℝ) (sentinel : ℝ)
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f)
    (hlt : ∀ x, value R f sentinel x < sentinel) :
    ∃ g : X → Y, Measurable g ∧
      ∀ x, R x (g x) ∧ f (g x) = value R f sentinel x ∧
        ∀ y, R x y → f (g x) ≤ f y := by
  obtain ⟨g, hg, hmem⟩ :=
    Tournament.Probability.exists_measurable_selector_of_closed_hits
      (optimizers R f sentinel)
      (fun x ↦ optimizers_nonempty hR hf x (hlt x))
      (optimizers_closed hR hf)
      (fun C hC ↦ optimizers_hit_measurableSet hR hf hlt hC)
  refine ⟨g, hg, ?_⟩
  intro x
  refine ⟨(hmem x).1, (hmem x).2, ?_⟩
  intro y hy
  rw [(hmem x).2]
  exact value_le_cost hR hf x y hy

theorem exists_measurable_minimizer
    (R : X → Y → Prop) (f : Y → ℝ)
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f)
    (hNonempty : ∀ x, ∃ y, R x y) :
    ∃ g : X → Y, Measurable g ∧
      ∀ x, R x (g x) ∧ ∀ y, R x y → f (g x) ≤ f y := by
  obtain ⟨b, hb⟩ := (isCompact_univ.image hf).bddAbove
  have hBound (y : Y) : f y < b + 1 :=
    lt_of_le_of_lt (hb ⟨y, Set.mem_univ y, rfl⟩) (lt_add_one b)
  have hlt (x : X) : value R f (b + 1) x < b + 1 := by
    obtain ⟨y, hy⟩ := hNonempty x
    exact (value_le_cost hR hf x y hy).trans_lt (hBound y)
  obtain ⟨g, hg, hopt⟩ := exists_measurable_optimizer_below_sentinel R f (b + 1) hR hf hlt
  exact ⟨g, hg, fun x ↦ ⟨(hopt x).1, (hopt x).2.2⟩⟩

end

section CompactSubset

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X] [MetricSpace Y] [SeparableSpace Y]
variable [MeasurableSpace Y] [BorelSpace Y]

theorem exists_measurable_minimizer_on_compact
    (K : Set Y) (hK : IsCompact K) (hKne : K.Nonempty)
    (R : X → Y → Prop) (f : Y → ℝ)
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f)
    (hNonempty : ∀ x, ∃ y ∈ K, R x y) :
    ∃ g : X → Y, Measurable g ∧
      ∀ x, g x ∈ K ∧ R x (g x) ∧ ∀ y ∈ K, R x y → f (g x) ≤ f y := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hKne.to_subtype
  have hRK : IsClosed {p : X × K | R p.1 p.2.val} :=
    hR.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfK : Continuous (fun y : K ↦ f y.val) := hf.comp continuous_subtype_val
  obtain ⟨g, hg, hopt⟩ := exists_measurable_minimizer
    (fun x (y : K) ↦ R x y.val) (fun y : K ↦ f y.val) hRK hfK
    (fun x ↦ by
      obtain ⟨y, hyK, hy⟩ := hNonempty x
      exact ⟨⟨y, hyK⟩, hy⟩)
  refine ⟨fun x ↦ (g x).val, measurable_subtype_coe.comp hg, ?_⟩
  intro x
  refine ⟨(g x).property, (hopt x).1, ?_⟩
  intro y hyK hy
  exact (hopt x).2 ⟨y, hyK⟩ hy

end CompactSubset

end Tournament.Probability.CompactOptimization
