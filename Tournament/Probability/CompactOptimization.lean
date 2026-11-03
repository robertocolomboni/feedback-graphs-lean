module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

namespace Tournament.Probability.CompactOptimization

open Set
open scoped Classical

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace Y]

def costSet (R : X → Y → Prop) (f : Y → ℝ) (sentinel : ℝ) (x : X) : Set ℝ :=
  insert sentinel (f '' {y | R x y})

def value (R : X → Y → Prop) (f : Y → ℝ) (sentinel : ℝ) (x : X) : ℝ :=
  sInf (costSet R f sentinel x)

variable {R : X → Y → Prop} {f : Y → ℝ} {sentinel : ℝ}

omit [CompactSpace Y] in
theorem fiber_closed (hR : IsClosed {p : X × Y | R p.1 p.2}) (x : X) :
    IsClosed {y | R x y} :=
  hR.preimage (continuous_const.prodMk continuous_id)

theorem costSet_compact (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) : IsCompact (costSet R f sentinel x) :=
  ((fiber_closed hR x).isCompact.image hf).insert sentinel

theorem value_isLeast (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) :
    IsLeast (costSet R f sentinel x) (value R f sentinel x) := by
  obtain ⟨a, ha⟩ := (costSet_compact hR hf x).exists_isLeast (by
    exact ⟨sentinel, Set.mem_insert _ _⟩)
  have heq : value R f sentinel x = a := ha.csInf_eq
  rw [heq]
  exact ha

theorem value_le_sentinel (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) : value R f sentinel x ≤ sentinel :=
  (value_isLeast hR hf x).2 (Set.mem_insert _ _)

theorem value_le_cost (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) (y : Y) (hy : R x y) :
    value R f sentinel x ≤ f y :=
  (value_isLeast hR hf x).2 (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)

theorem value_le_iff (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) (a : ℝ) :
    value R f sentinel x ≤ a ↔ sentinel ≤ a ∨ ∃ y, R x y ∧ f y ≤ a := by
  constructor
  · intro h
    rcases (value_isLeast (sentinel := sentinel) hR hf x).1 with hsent | ⟨y, hy, hfy⟩
    · exact Or.inl (hsent.symm.trans_le h)
    · exact Or.inr ⟨y, hy, hfy.trans_le h⟩
  · rintro (h | ⟨y, hy, hfy⟩)
    · exact (value_le_sentinel hR hf x).trans h
    · exact (value_le_cost hR hf x y hy).trans hfy

theorem exists_optimizer_of_value_lt (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) (hlt : value R f sentinel x < sentinel) :
    ∃ y, R x y ∧ f y = value R f sentinel x ∧ ∀ z, R x z → f y ≤ f z := by
  rcases (value_isLeast (sentinel := sentinel) hR hf x).1 with hsent | ⟨y, hy, hfy⟩
  · exact False.elim ((ne_of_lt hlt) hsent)
  · refine ⟨y, hy, hfy, ?_⟩
    intro z hz
    rw [hfy]
    exact value_le_cost hR hf x z hz

theorem isClosed_feasible_sublevel (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (a : ℝ) : IsClosed {x | ∃ y, R x y ∧ f y ≤ a} := by
  have hclosed : IsClosed {p : X × Y | R p.1 p.2 ∧ f p.2 ≤ a} :=
    hR.inter (isClosed_le (hf.comp continuous_snd) continuous_const)
  have heq : Prod.fst '' {p : X × Y | R p.1 p.2 ∧ f p.2 ≤ a} =
      {x | ∃ y, R x y ∧ f y ≤ a} := by
    ext x
    constructor
    · rintro ⟨⟨x', y⟩, h, rfl⟩
      exact ⟨y, h⟩
    · rintro ⟨y, h⟩
      exact ⟨(x, y), h, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace _ hclosed

theorem isClosed_value_sublevel (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (a : ℝ) : IsClosed {x | value R f sentinel x ≤ a} := by
  by_cases hs : sentinel ≤ a
  · have heq : {x | value R f sentinel x ≤ a} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (value_le_sentinel hR hf x).trans hs
    rw [heq]
    exact isClosed_univ
  · have heq : {x | value R f sentinel x ≤ a} = {x | ∃ y, R x y ∧ f y ≤ a} := by
      ext x
      simp only [Set.mem_ofPred_eq, value_le_iff hR hf, hs, false_or]
    rw [heq]
    exact isClosed_feasible_sublevel hR hf a

theorem value_measurable [MeasurableSpace X] [OpensMeasurableSpace X]
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f) :
    Measurable (value R f sentinel) := by
  apply measurable_of_Iic
  intro a
  exact (isClosed_value_sublevel hR hf a).measurableSet

omit [CompactSpace Y] in

theorem restricted_relation_closed (hR : IsClosed {p : X × Y | R p.1 p.2})
    {C : Set Y} (hC : IsClosed C) :
    IsClosed {p : X × Y | R p.1 p.2 ∧ p.2 ∈ C} :=
  hR.inter (hC.preimage continuous_snd)

def restrictedValue (R : X → Y → Prop) (f : Y → ℝ) (sentinel : ℝ)
    (C : Set Y) (x : X) : ℝ :=
  value (fun x y ↦ R x y ∧ y ∈ C) f sentinel x

theorem value_le_restrictedValue (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) {C : Set Y} (hC : IsClosed C) (x : X) :
    value R f sentinel x ≤ restrictedValue R f sentinel C x := by
  rcases (value_isLeast (R := fun x y ↦ R x y ∧ y ∈ C)
    (sentinel := sentinel) (restricted_relation_closed hR hC) hf x).1 with
      hsent | ⟨y, hy, hfy⟩
  · change value R f sentinel x ≤ value (fun x y ↦ R x y ∧ y ∈ C) f sentinel x
    rw [hsent]
    exact value_le_sentinel hR hf x
  · change value R f sentinel x ≤ value (fun x y ↦ R x y ∧ y ∈ C) f sentinel x
    rw [← hfy]
    exact value_le_cost hR hf x y hy.1

theorem restrictedValue_measurable [MeasurableSpace X] [OpensMeasurableSpace X]
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f)
    {C : Set Y} (hC : IsClosed C) : Measurable (restrictedValue R f sentinel C) :=
  value_measurable (restricted_relation_closed hR hC) hf

def optimizers (R : X → Y → Prop) (f : Y → ℝ) (sentinel : ℝ) (x : X) : Set Y :=
  {y | R x y ∧ f y = value R f sentinel x}

omit [CompactSpace Y] in
theorem optimizers_closed (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) : IsClosed (optimizers R f sentinel x) :=
  (fiber_closed hR x).inter (isClosed_eq hf continuous_const)

theorem optimizers_nonempty (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) (x : X) (hlt : value R f sentinel x < sentinel) :
    (optimizers R f sentinel x).Nonempty := by
  obtain ⟨y, hy, hfy, _⟩ := exists_optimizer_of_value_lt hR hf x hlt
  exact ⟨y, hy, hfy⟩

theorem optimizers_hit_iff (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hf : Continuous f) {C : Set Y} (hC : IsClosed C) (x : X)
    (hlt : value R f sentinel x < sentinel) :
    (optimizers R f sentinel x ∩ C).Nonempty ↔
      restrictedValue R f sentinel C x = value R f sentinel x := by
  constructor
  · rintro ⟨y, ⟨hy, hfy⟩, hyC⟩
    apply le_antisymm
    · exact (value_le_cost (restricted_relation_closed hR hC) hf x y ⟨hy, hyC⟩).trans_eq hfy
    · exact value_le_restrictedValue hR hf hC x
  · intro heq
    have hlt' : value (fun x y ↦ R x y ∧ y ∈ C) f sentinel x < sentinel :=
      heq.trans_lt hlt
    obtain ⟨y, ⟨hy, hyC⟩, hfy, _⟩ :=
      exists_optimizer_of_value_lt (restricted_relation_closed hR hC) hf x hlt'
    exact ⟨y, ⟨hy, hfy.trans heq⟩, hyC⟩

theorem optimizers_hit_measurableSet [MeasurableSpace X] [OpensMeasurableSpace X]
    (hR : IsClosed {p : X × Y | R p.1 p.2}) (hf : Continuous f)
    (hlt : ∀ x, value R f sentinel x < sentinel) {C : Set Y} (hC : IsClosed C) :
    MeasurableSet {x | (optimizers R f sentinel x ∩ C).Nonempty} := by
  have heq : {x | (optimizers R f sentinel x ∩ C).Nonempty} =
      {x | restrictedValue R f sentinel C x = value R f sentinel x} := by
    ext x
    exact optimizers_hit_iff hR hf hC x (hlt x)
  rw [heq]
  exact measurableSet_eq_fun (restrictedValue_measurable hR hf hC) (value_measurable hR hf)

end
end Tournament.Probability.CompactOptimization
