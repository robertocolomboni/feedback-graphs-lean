module

public import Tournament.Probability.OrderedMoments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace Tournament.FilteredMoments

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter OrderedMoments

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem adapted_sum {α : Type*} {m : MeasurableSpace Ω} (s : Finset α) (f : α → Ω → ℝ)
    (hf : ∀ a ∈ s, AEStronglyMeasurable[m] (f a) μ) :
    AEStronglyMeasurable[m] (fun ω ↦ ∑ a ∈ s, f a ω) μ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact aestronglyMeasurable_const
  | @insert a s ha ih =>
    have hs := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have h := (hf a (Finset.mem_insert_self _ _)).fun_add hs
    simpa only [Finset.sum_insert ha] using h

theorem bounded_integrable (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (c : ℝ)
    (hc : ∀ ω, |f ω|≤c) : Integrable f μ := by
  apply (integrable_const c).mono' hf
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hc ω)

omit μ [IsProbabilityMeasure μ] mΩ in
theorem ordered_bound (y : ℕ → ℝ) (N : ℕ) (b : ℝ) (hb : 0≤b)
    (hy0 : ∀ t, 0≤y t) (hy : ∀ t, t<N → y t≤b) (k n : ℕ) (hn : n≤N) :
    orderedProducts y k n≤((N:ℝ)*b)^k := by
  induction k generalizing n with
  | zero => simp [orderedProducts]
  | succ k ih =>
    calc
      _ ≤ ∑ _t ∈ Finset.range n, b*((N:ℝ)*b)^k := by
        apply Finset.sum_le_sum
        intro t ht
        have ht' : t<n := Finset.mem_range.mp ht
        exact mul_le_mul (hy t (by omega)) (ih (t+1) (by omega))
          (orderedProducts_nonneg y hy0 k (t+1)) hb
      _ = (n:ℝ)*b*((N:ℝ)*b)^k := by simp; ring
      _ ≤ (N:ℝ)*b*((N:ℝ)*b)^k := by gcongr
      _ = _ := by rw [pow_succ]; ring

omit [IsProbabilityMeasure μ] in
theorem ordered_adapted (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (k n p : ℕ) (hn : n≤N) (hnp : n≤p) :
    AEStronglyMeasurable[history p] (fun ω ↦ orderedProducts (fun t ↦ Y t ω) k n) μ := by
  let : MeasurableSpace Ω := mΩ
  induction k generalizing n with
  | zero =>
    change AEStronglyMeasurable[history p] (fun _ : Ω ↦ (1:ℝ)) μ
    exact aestronglyMeasurable_const
  | succ k ih =>
    apply adapted_sum μ (Finset.range n)
    intro t ht
    have ht' : t<n := Finset.mem_range.mp ht
    have htY : AEStronglyMeasurable[history p] (Y t) μ :=
      AEStronglyMeasurable.mono (hmono (show t+1≤p by omega)) (hY t (by omega))
    exact htY.fun_mul (ih (t+1) (by omega) (by omega))

theorem ordered_integrable (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b : ℝ) (hb : 0≤b)
    (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b) (k n : ℕ) (hn : n≤N) :
    Integrable (fun ω ↦ orderedProducts (fun t ↦ Y t ω) k n) μ := by
  have hm : AEStronglyMeasurable[mΩ] (fun ω ↦ orderedProducts (fun t ↦ Y t ω) k n) μ :=
    AEStronglyMeasurable.mono (hglobal n) (ordered_adapted μ history hmono Y N hY k n n hn le_rfl)
  apply bounded_integrable μ _ hm (((N:ℝ)*b)^k)
  intro ω
  rw [abs_of_nonneg (orderedProducts_nonneg _ (fun t ↦ hY0 t ω) k n)]
  exact ordered_bound (fun t ↦ Y t ω) N b hb (fun t ↦ hY0 t ω) (fun t ht ↦ hbound t ht ω) k n hn

theorem bounded_conditional_product (m : MeasurableSpace Ω) (hm : m≤mΩ)
    (Z f : Ω → ℝ) (hZ : AEStronglyMeasurable[m] Z μ) (c : ℝ) (hZc : ∀ ω, |Z ω|≤c)
    (hZ0 : ∀ ω, 0≤Z ω) (hf : Integrable f μ) (v : ℝ)
    (hcond : μ[f | m] ≤ᵐ[μ] fun _ ↦ v) :
    (∫ ω, Z ω*f ω ∂μ)≤v*(∫ ω, Z ω ∂μ) := by
  let : MeasurableSpace Ω := mΩ
  have hZ' : AEStronglyMeasurable[mΩ] Z μ := AEStronglyMeasurable.mono hm hZ
  have hZInt := bounded_integrable μ Z hZ' c hZc
  have hZbound : ∀ᵐ ω ∂μ, ‖Z ω‖≤c := Eventually.of_forall (fun ω ↦ by
    simpa only [Real.norm_eq_abs] using hZc ω)
  have hZf : Integrable (fun ω ↦ Z ω*f ω) μ := hf.bdd_mul hZ' hZbound
  have hZce : Integrable (fun ω ↦ Z ω*(μ[f | m]) ω) μ := integrable_condExp.bdd_mul hZ' hZbound
  have hZv : Integrable (fun ω ↦ Z ω*v) μ := hZInt.mul_const v
  calc
    _ = ∫ ω, (μ[fun x ↦ Z x*f x | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, Z ω*(μ[f | m]) ω ∂μ := integral_congr_ae
      (condExp_mul_of_aestronglyMeasurable_left hZ hZf hf)
    _ ≤ ∫ ω, Z ω*v ∂μ := integral_mono_ae hZce hZv (hcond.mono (fun ω hω ↦
      mul_le_mul_of_nonneg_left hω (hZ0 ω)))
    _ = _ := by rw [integral_mul_const]; ring

theorem variable_integrable (history : ℕ → MeasurableSpace Ω)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b : ℝ) (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b)
    (t : ℕ) (ht : t<N) : Integrable (Y t) μ := by
  have hm : AEStronglyMeasurable[mΩ] (Y t) μ := AEStronglyMeasurable.mono (hglobal (t+1)) (hY t ht)
  apply bounded_integrable μ (Y t) hm (max b 0)
  intro ω
  rw [abs_of_nonneg (hY0 t ω)]
  exact le_trans (hbound t ht ω) (le_max_left b 0)

theorem future_integrable (history : ℕ → MeasurableSpace Ω)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b : ℝ) (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b) (t : ℕ) :
    Integrable (fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0) μ := by
  apply integrable_finsetSum
  intro u hu
  by_cases htu : t<u
  · simp only [ite_eq_left htu]
    exact variable_integrable μ history hglobal Y N hY hY0 b hbound u (Finset.mem_range.mp hu)
  · simp only [ite_eq_right htu]
    exact integrable_zero _ _ _

theorem ordered_step_integral (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b v : ℝ)
    (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v) (k : ℕ) :
    (∫ ω, orderedProducts (fun t ↦ Y t ω) (k+2) N ∂μ)≤
      (b+v)*(∫ ω, orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ) := by
  let : MeasurableSpace Ω := mΩ
  let c := max b 0
  have hc : 0≤c := le_max_right b 0
  have hbc (t : ℕ) (ht : t<N) (ω : Ω) : Y t ω≤c := (hbound t ht ω).trans (le_max_left b 0)
  let Z := fun t ω ↦ Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1)
  let tail := fun t ω ↦ inclusiveTail (fun u ↦ Y u ω) N t
  have hZ0 (t : ℕ) (ω : Ω) : 0≤Z t ω :=
    mul_nonneg (hY0 t ω) (orderedProducts_nonneg _ (fun u ↦ hY0 u ω) k (t+1))
  have hZadapt (t : ℕ) (ht : t<N) : AEStronglyMeasurable[history (t+1)] (Z t) μ :=
    (hY t ht).fun_mul (ordered_adapted μ history hmono Y N hY k (t+1) (t+1) (by omega) le_rfl)
  have hZbound (t : ℕ) (ht : t<N) (ω : Ω) : |Z t ω|≤c*((N:ℝ)*c)^k := by
    rw [abs_of_nonneg (hZ0 t ω)]
    exact mul_le_mul (hbc t ht ω)
      (ordered_bound (fun u ↦ Y u ω) N c hc (fun u ↦ hY0 u ω) (fun u hu ↦ hbc u hu ω)
        k (t+1) (by omega))
      (orderedProducts_nonneg _ (fun u ↦ hY0 u ω) k (t+1)) hc
  have hZInt (t : ℕ) (ht : t<N) : Integrable (Z t) μ :=
    bounded_integrable μ (Z t) (AEStronglyMeasurable.mono (hglobal (t+1)) (hZadapt t ht))
      (c*((N:ℝ)*c)^k) (hZbound t ht)
  have htailInt (t : ℕ) (ht : t<N) : Integrable (tail t) μ := by
    have hs : tail t=(fun ω ↦ Y t ω+∑ u ∈ Finset.range N, if t<u then Y u ω else 0) :=
      funext (fun ω ↦ inclusiveTail_split (fun u ↦ Y u ω) N t ht)
    rw [hs]
    exact (variable_integrable μ history hglobal Y N hY hY0 b hbound t ht).add
      (future_integrable μ history hglobal Y N hY hY0 b hbound t)
  have htailCE (t : ℕ) (ht : t<N) : μ[tail t | history (t+1)] ≤ᵐ[μ] fun _ ↦ b+v := by
    have hs : tail t=(fun ω ↦ Y t ω+∑ u ∈ Finset.range N, if t<u then Y u ω else 0) :=
      funext (fun ω ↦ inclusiveTail_split (fun u ↦ Y u ω) N t ht)
    have hYint := variable_integrable μ history hglobal Y N hY hY0 b hbound t ht
    have hfint := future_integrable μ history hglobal Y N hY hY0 b hbound t
    have hyce := condExp_of_aestronglyMeasurable' (hglobal (t+1)) (hY t ht) hYint
    have hsum := condExp_add hYint hfint (history (t+1))
    rw [hs]
    filter_upwards [hsum,hyce,hfuture t ht] with ω hω hy hf
    change (μ[fun ω ↦ Y t ω+∑ u ∈ Finset.range N, if t<u then Y u ω else 0 | history (t+1)]) ω=
      (μ[Y t | history (t+1)]) ω+
        (μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 | history (t+1)]) ω at hω
    rw [hω,hy]
    linarith [hbound t ht ω]
  have hprodInt (t : ℕ) (ht : t<N) : Integrable (fun ω ↦ Z t ω*tail t ω) μ :=
    (htailInt t ht).bdd_mul (AEStronglyMeasurable.mono (hglobal (t+1)) (hZadapt t ht))
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hZbound t ht ω))
  have heq : (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+2) N)=
      (fun ω ↦ ∑ t ∈ Finset.range N, Z t ω*tail t ω) :=
    funext (fun ω ↦ orderedProducts_last_index (fun t ↦ Y t ω) k N)
  rw [heq,integral_finsetSum _ (fun t ht ↦ hprodInt t (Finset.mem_range.mp ht))]
  calc
    _ ≤ ∑ t ∈ Finset.range N, (b+v)*(∫ ω, Z t ω ∂μ) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      exact bounded_conditional_product μ (history (t+1)) (hglobal (t+1)) (Z t) (tail t)
        (hZadapt t ht') (c*((N:ℝ)*c)^k) (hZbound t ht') (hZ0 t) (htailInt t ht') (b+v) (htailCE t ht')
    _ = (b+v)*(∫ ω, orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ) := by
      rw [← Finset.mul_sum,← integral_finsetSum _ (fun t ht ↦ hZInt t (Finset.mem_range.mp ht))]
      rfl

theorem ordered_integral_bound (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b v : ℝ) (hB : 0≤b+v)
    (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v) (k : ℕ) :
    (∫ ω, orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ)≤
      (b+v)^k*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add,pow_zero,one_mul,orderedProducts_one]
    exact le_rfl
  | succ k ih =>
    calc
      _ ≤ (b+v)*(∫ ω, orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ) :=
        ordered_step_integral μ history hmono hglobal Y N hY hY0 b v hbound hfuture k
      _ ≤ (b+v)*((b+v)^k*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)) :=
        mul_le_mul_of_nonneg_left ih hB
      _ = _ := by rw [pow_succ]; ring

omit μ [IsProbabilityMeasure μ] mΩ in
theorem total_bounds (Y : ℕ → Ω → ℝ) (N : ℕ) (hY0 : ∀ t ω, 0≤Y t ω)
    (b : ℝ) (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b) (ω : Ω) :
    0≤(∑ t ∈ Finset.range N, Y t ω) ∧ (∑ t ∈ Finset.range N, Y t ω)≤(N:ℝ)*max b 0 := by
  constructor
  · exact Finset.sum_nonneg (fun t _ ↦ hY0 t ω)
  · calc
      _ ≤ ∑ _t ∈ Finset.range N, max b 0 := Finset.sum_le_sum (fun t ht ↦
        (hbound t (Finset.mem_range.mp ht) ω).trans (le_max_left b 0))
      _ = _ := by simp

theorem accumulated_moment_integral (history : ℕ → MeasurableSpace Ω) (hmono : Monotone history)
    (hglobal : ∀ t, history t≤mΩ) (Y : ℕ → Ω → ℝ) (N : ℕ)
    (hY : ∀ t, t<N → AEStronglyMeasurable[history (t+1)] (Y t) μ)
    (hY0 : ∀ t ω, 0≤Y t ω) (b v : ℝ) (hB : 0≤b+v)
    (hbound : ∀ t, t<N → ∀ ω, Y t ω≤b)
    (hfuture : ∀ t, t<N → μ[fun ω ↦ ∑ u ∈ Finset.range N, if t<u then Y u ω else 0 |
      history (t+1)] ≤ᵐ[μ] fun _ ↦ v) (k : ℕ) :
    (∫ ω, (∑ t ∈ Finset.range N, Y t ω)^(k+1) ∂μ)≤
      (Nat.factorial (k+1):ℝ)*(b+v)^k*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ) := by
  have hV : Integrable (fun ω ↦ ∑ t ∈ Finset.range N, Y t ω) μ :=
    integrable_finsetSum _ (fun t ht ↦ variable_integrable μ history hglobal Y N hY hY0 b hbound t (Finset.mem_range.mp ht))
  have hpower : Integrable (fun ω ↦ (∑ t ∈ Finset.range N, Y t ω)^(k+1)) μ := by
    apply bounded_integrable μ (fun ω ↦ (∑ t ∈ Finset.range N, Y t ω)^(k+1))
      (hV.aestronglyMeasurable.pow (k+1)) (((N:ℝ)*max b 0)^(k+1))
    intro ω
    have hv := total_bounds Y N hY0 b hbound ω
    rw [abs_of_nonneg (pow_nonneg hv.1 (k+1))]
    exact pow_le_pow_left₀ hv.1 hv.2 (k+1)
  have hO : Integrable (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) N) μ :=
    ordered_integrable μ history hmono hglobal Y N hY hY0 (max b 0) (le_max_right b 0)
      (fun t ht ω ↦ (hbound t ht ω).trans (le_max_left b 0)) (k+1) N le_rfl
  calc
    _ ≤ ∫ ω, (Nat.factorial (k+1):ℝ)*orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ :=
      integral_mono_ae hpower (hO.const_mul _) (Eventually.of_forall (fun ω ↦
        sum_pow_le_factorial_ordered (fun t ↦ Y t ω) (fun t ↦ hY0 t ω) (k+1) N))
    _ = (Nat.factorial (k+1):ℝ)*(∫ ω, orderedProducts (fun t ↦ Y t ω) (k+1) N ∂μ) := integral_const_mul _ _
    _ ≤ (Nat.factorial (k+1):ℝ)*((b+v)^k*(∫ ω, (∑ t ∈ Finset.range N, Y t ω) ∂μ)) :=
      mul_le_mul_of_nonneg_left (ordered_integral_bound μ history hmono hglobal Y N hY hY0 b v hB hbound hfuture k)
        (Nat.cast_nonneg _)
    _ = _ := by ring

end
end Tournament.FilteredMoments
