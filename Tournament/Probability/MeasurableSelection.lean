module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

namespace Tournament.Probability

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

theorem exists_measurable_selector_of_closedBall_hits
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y] [CompleteSpace Y]
    [SeparableSpace Y] [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y]
    (S : X → Set Y) (hNonempty : ∀ x, (S x).Nonempty)
    (hClosed : ∀ x, IsClosed (S x))
    (hHit : ∀ y : Y, ∀ r : ℝ,
      MeasurableSet {x | (S x ∩ Metric.closedBall y r).Nonempty}) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, f x ∈ S x := by
  classical
  let c : ℕ → Y := denseSeq Y
  have hc : DenseRange c := denseRange_denseSeq Y
  let r : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hr_pos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr_succ (n : ℕ) : r (n + 1) = r n / 2 := by
    simp only [r, pow_succ]
    ring
  have hr_tendsto : Tendsto r atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let good (n : ℕ) (x : X) (y : Y) : Prop :=
    (S x ∩ Metric.closedBall y (r n)).Nonempty
  have hgood_meas (n i : ℕ) : MeasurableSet {x | good n x (c i)} :=
    hHit (c i) (r n)
  have hbase (x : X) : ∃ i, good 0 x (c i) := by
    obtain ⟨z, hz⟩ := hNonempty x
    obtain ⟨i, hi⟩ := hc.exists_dist_lt z (hr_pos 0)
    exact ⟨i, z, hz, hi.le⟩
  let base : X → Y := fun x ↦ c (Nat.find (hbase x))
  have hbase_meas : Measurable base :=
    (measurable_of_countable c).comp (measurable_find hbase (hgood_meas 0))
  have hbase_good (x : X) : good 0 x (base x) := Nat.find_spec (hbase x)
  have hstep (n : ℕ) (p : X → Y) (hp_meas : Measurable p)
      (hp_good : ∀ x, good n x (p x)) :
      ∃ q : X → Y, Measurable q ∧ (∀ x, good (n + 1) x (q x)) ∧
        ∀ x, dist (p x) (q x) ≤ 2 * r n := by
    let P (x : X) (i : ℕ) : Prop :=
      good (n + 1) x (c i) ∧ dist (p x) (c i) < 2 * r n
    have hP_exists (x : X) : ∃ i, P x i := by
      obtain ⟨z, hzS, hzp⟩ := hp_good x
      obtain ⟨i, hi⟩ := hc.exists_dist_lt z (hr_pos (n + 1))
      refine ⟨i, ⟨⟨z, hzS, hi.le⟩, ?_⟩⟩
      have hzp' : dist (p x) z ≤ r n := by
        simpa only [Metric.mem_closedBall, dist_comm] using hzp
      have htri := dist_triangle (p x) z (c i)
      have hrn := hr_pos n
      rw [hr_succ] at hi
      linarith
    have hP_meas (i : ℕ) : MeasurableSet {x | P x i} :=
      (hgood_meas (n + 1) i).inter
        (measurableSet_lt (hp_meas.dist measurable_const) measurable_const)
    let q : X → Y := fun x ↦ c (Nat.find (hP_exists x))
    refine ⟨q, (measurable_of_countable c).comp (measurable_find hP_exists hP_meas),
      ?_, ?_⟩
    · intro x
      exact (Nat.find_spec (hP_exists x)).1
    · intro x
      exact (Nat.find_spec (hP_exists x)).2.le
  let F : ∀ n : ℕ, {p : X → Y // Measurable p ∧ ∀ x, good n x (p x)} :=
    fun n ↦ Nat.rec ⟨base, hbase_meas, hbase_good⟩
      (fun n p ↦ ⟨(hstep n p.1 p.2.1 p.2.2).choose,
        (hstep n p.1 p.2.1 p.2.2).choose_spec.1,
        (hstep n p.1 p.2.1 p.2.2).choose_spec.2.1⟩) n
  have hF_dist (n : ℕ) (x : X) : dist ((F n).1 x) ((F (n + 1)).1 x) ≤ 2 * r n :=
    (hstep n (F n).1 (F n).2.1 (F n).2.2).choose_spec.2.2 x
  have hF_limit (x : X) : ∃ y, Tendsto (fun n ↦ (F n).1 x) atTop (𝓝 y) := by
    apply cauchySeq_tendsto_of_complete
    exact cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (fun n ↦ hF_dist n x)
  let f : X → Y := fun x ↦ (hF_limit x).choose
  have hf_limit (x : X) : Tendsto (fun n ↦ (F n).1 x) atTop (𝓝 (f x)) :=
    (hF_limit x).choose_spec
  refine ⟨f, measurable_of_tendsto_metrizable (fun n ↦ (F n).2.1)
    (tendsto_pi_nhds.mpr hf_limit), ?_⟩
  intro x
  have hw (n : ℕ) : ∃ z ∈ S x, dist ((F n).1 x) z ≤ r n := by
    obtain ⟨z, hzS, hz⟩ := (F n).2.2 x
    exact ⟨z, hzS, by simpa only [Metric.mem_closedBall, dist_comm] using hz⟩
  choose z hzS hzdist using hw
  have hz_limit : Tendsto z atTop (𝓝 (f x)) :=
    (hf_limit x).congr_dist (squeeze_zero (fun _ ↦ dist_nonneg) hzdist hr_tendsto)
  exact (hClosed x).mem_of_tendsto hz_limit (Eventually.of_forall hzS)

theorem exists_measurable_selector_of_closed_hits
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y] [CompleteSpace Y]
    [SeparableSpace Y] [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y]
    (S : X → Set Y) (hNonempty : ∀ x, (S x).Nonempty)
    (hClosed : ∀ x, IsClosed (S x))
    (hHit : ∀ C : Set Y, IsClosed C → MeasurableSet {x | (S x ∩ C).Nonempty}) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, f x ∈ S x :=
  exists_measurable_selector_of_closedBall_hits S hNonempty hClosed
    (fun y r ↦ hHit (Metric.closedBall y r) Metric.isClosed_closedBall)

end

end Tournament.Probability
