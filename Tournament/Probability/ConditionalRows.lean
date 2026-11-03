module

public import Tournament.Probability.VectorKernel
public import Tournament.Probability.FiniteConditional
public import Tournament.Probability.Extensionality
public import Tournament.Upper.ExponentialWeights
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace Tournament.ConditionalRows

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

noncomputable section

def finiteMap {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : ProbabilityVector Ω) (f : Ω → Ξ) : ProbabilityVector Ξ where
  weight z := FiniteConditional.fiberMass μ f z
  nonneg z := Finset.sum_nonneg (fun x _ ↦ by
    split
    · exact μ.nonneg x
    · exact le_rfl)
  sum_eq_one := by
    unfold FiniteConditional.fiberMass
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using μ.sum_eq_one

variable {Meta ι : Type*} {T : ℕ}

def takePrefix (t : ℕ) (ht : t ≤ T) (x : Meta × (Fin T → ι)) : Meta × (Fin t → ι) :=
  (x.1, fun j ↦ x.2 (j.castLE ht))

theorem prefix_succ (t : ℕ) (ht : t < T) (x : Meta × (Fin T → ι)) :
    takePrefix (t+1) (by omega) x =
      (x.1, Fin.snoc (takePrefix t (by omega) x).2 (x.2 ⟨t,ht⟩)) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [takePrefix, Fin.snoc_last]
      exact congrArg x.2 (Fin.ext rfl)
    · simp [takePrefix]

theorem prefix_full (x : Meta × (Fin T → ι)) : takePrefix T le_rfl x = x := by
  rcases x with ⟨q,a⟩
  rfl

variable [Fintype Meta] [Fintype ι]

def prefixMass (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t ≤ T) (q : Meta) (a : Fin t → ι) : ℝ :=
  FiniteConditional.fiberMass μ (takePrefix t ht) (q,a)

theorem prefixMass_nonneg (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t ≤ T) (q : Meta) (a : Fin t → ι) :
    0 ≤ prefixMass μ t ht q a := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonneg x
  · exact le_rfl

theorem prefixMass_full (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (q : Meta) (a : Fin T → ι) : prefixMass μ T le_rfl q a = μ (q,a) := by
  simp [prefixMass, FiniteConditional.fiberMass, prefix_full]

def prefixLaw (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t ≤ T) : ProbabilityVector (Meta × (Fin t → ι)) :=
  finiteMap μ (takePrefix t ht)

theorem prefixLaw_apply (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t ≤ T) (q : Meta) (a : Fin t → ι) :
    prefixLaw μ t ht (q,a) = prefixMass μ t ht q a := rfl

def firstRow (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (hT : 0 < T) : ProbabilityVector (Meta × ι) :=
  finiteMap μ (fun x ↦ (x.1, x.2 ⟨0,hT⟩))

theorem firstRow_apply (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (hT : 0 < T) (q : Meta) (i : ι) :
    firstRow μ hT (q,i) = prefixMass μ 1 (by omega) q (fun _ ↦ i) := by
  unfold firstRow finiteMap prefixMass FiniteConditional.fiberMass
  apply Finset.sum_congr rfl
  intro x _
  have hp : takePrefix 1 (by omega) x = (q,fun _ ↦ i) ↔
      (x.1,x.2 ⟨0,hT⟩) = (q,i) := by
    simp only [takePrefix, Prod.mk.injEq, funext_iff, Fin.forall_fin_one]
    rfl
  rw [hp]

theorem firstRow_eq_of_prefixMass (μ ν : ProbabilityVector (Meta × (Fin T → ι)))
    (hT : 0 < T)
    (h : ∀ q i, prefixMass μ 1 (by omega) q (fun _ ↦ i) =
      prefixMass ν 1 (by omega) q (fun _ ↦ i)) : firstRow μ hT = firstRow ν hT := by
  apply ProbabilityVector.ext_weights
  intro x
  rw [firstRow_apply μ hT x.1 x.2, firstRow_apply ν hT x.1 x.2]
  exact h x.1 x.2

theorem prefixMass_sum_snoc (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) :
    ∑ i, prefixMass μ (t+1) (by omega) q (Fin.snoc a i) =
      prefixMass μ t (by omega) q a := by
  unfold prefixMass FiniteConditional.fiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [prefix_succ t ht x, Fin.snoc_inj, Prod.ext_iff]
  change (∑ i, if x.1 = q ∧ ((takePrefix t (by omega) x).2 = a ∧ x.2 ⟨t,ht⟩ = i)
    then μ x else 0) = if x.1 = q ∧ (takePrefix t (by omega) x).2 = a then μ x else 0
  by_cases hq : x.1 = q
  · by_cases ha : (takePrefix t (by omega) x).2 = a
    · simp [hq, ha]
    · simp [hq, ha]
  · simp [hq]

theorem prefixMass_snoc_le (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) (i : ι) :
    prefixMass μ (t+1) (by omega) q (Fin.snoc a i) ≤ prefixMass μ t (by omega) q a := by
  rw [← prefixMass_sum_snoc μ t ht q a]
  exact Finset.single_le_sum (fun j _ ↦ prefixMass_nonneg μ _ _ q (Fin.snoc a j))
    (Finset.mem_univ i)

theorem prefixMass_snoc_eq_zero (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι)
    (hz : prefixMass μ t (by omega) q a = 0) (i : ι) :
    prefixMass μ (t+1) (by omega) q (Fin.snoc a i) = 0 := by
  apply le_antisymm
  · simpa only [hz] using prefixMass_snoc_le μ t ht q a i
  · exact prefixMass_nonneg μ _ _ q (Fin.snoc a i)

variable [Nonempty ι]

def nextRow (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) : ProbabilityVector ι :=
  if hd : 0 < prefixMass μ t (by omega) q a then {
    weight i := prefixMass μ (t+1) (by omega) q (Fin.snoc a i) /
      prefixMass μ t (by omega) q a
    nonneg i := div_nonneg (prefixMass_nonneg μ _ _ q (Fin.snoc a i)) hd.le
    sum_eq_one := by
      rw [← Finset.sum_div, prefixMass_sum_snoc μ t ht q a, div_self hd.ne']
  } else Upper.ExponentialWeights.uniform

theorem nextRow_apply (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) (i : ι) :
    nextRow μ t ht q a i = if 0 < prefixMass μ t (by omega) q a then
      prefixMass μ (t+1) (by omega) q (Fin.snoc a i) / prefixMass μ t (by omega) q a
      else 1 / (Fintype.card ι : ℝ) := by
  unfold nextRow
  split <;> rfl

theorem mass_mul_nextRow (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) (i : ι) :
    prefixMass μ t (by omega) q a * nextRow μ t ht q a i =
      prefixMass μ (t+1) (by omega) q (Fin.snoc a i) := by
  rw [nextRow_apply]
  by_cases hd : 0 < prefixMass μ t (by omega) q a
  · rw [ite_eq_left hd, mul_div_cancel₀ _ hd.ne']
  · have hz : prefixMass μ t (by omega) q a = 0 :=
      le_antisymm (le_of_not_gt hd) (prefixMass_nonneg μ t (by omega) q a)
    rw [hz, zero_mul, prefixMass_snoc_eq_zero μ t ht q a hz i]

theorem nextRow_eq_of_nextMass (μ ν : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι)
    (h : ∀ i, prefixMass μ (t+1) (by omega) q (Fin.snoc a i) =
      prefixMass ν (t+1) (by omega) q (Fin.snoc a i)) :
    nextRow μ t ht q a = nextRow ν t ht q a := by
  have hd : prefixMass μ t (by omega) q a = prefixMass ν t (by omega) q a := by
    rw [← prefixMass_sum_snoc μ t ht q a, ← prefixMass_sum_snoc ν t ht q a]
    exact Finset.sum_congr rfl (fun i _ ↦ h i)
  apply ProbabilityVector.ext_weights
  intro i
  simp only [nextRow_apply, hd, h i]

section Measurability

variable {A : Type*} [MeasurableSpace A]

omit [Nonempty ι] in
theorem prefixMass_measurable
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (t : ℕ) (ht : t ≤ T) (q : Meta) (a : Fin t → ι) :
    Measurable (fun z ↦ prefixMass (μ z) t ht q a) := by
  apply Finset.measurable_sum
  intro x _
  by_cases h : takePrefix t ht x = (q,a)
  · simp only [ite_eq_left h]
    exact hμ x
  · simp only [ite_eq_right h]
    exact measurable_const

omit [Nonempty ι] in
theorem firstRow_weight_measurable
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (hT : 0 < T) (v : Meta × ι) : Measurable (fun z ↦ firstRow (μ z) hT v) := by
  change Measurable (fun z ↦ firstRow (μ z) hT (v.1,v.2))
  simp_rw [firstRow_apply]
  exact prefixMass_measurable μ hμ 1 (by omega) v.1 (fun _ ↦ v.2)

theorem nextRow_weight_measurable
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) (i : ι) :
    Measurable (fun z ↦ nextRow (μ z) t ht q a i) := by
  simp_rw [nextRow_apply]
  exact Measurable.ite
    (measurableSet_lt measurable_const (prefixMass_measurable μ hμ t (by omega) q a))
    ((prefixMass_measurable μ hμ (t+1) (by omega) q (Fin.snoc a i)).div
      (prefixMass_measurable μ hμ t (by omega) q a)) measurable_const

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

variable [MeasurableSpace Meta] [DiscreteMeasurableSpace Meta]

omit [Nonempty ι] in
theorem prefixMass_measurable_varying
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) (t : ℕ) (ht : t ≤ T)
    (q : A → Meta) (hq : Measurable q) (a : A → Fin t → ι) (ha : Measurable a) :
    Measurable (fun z ↦ prefixMass (μ z) t ht (q z) (a z)) := by
  apply Finset.measurable_sum
  intro x _
  exact (hμ x).ite (measurableSet_eq_fun measurable_const (hq.prodMk ha)) measurable_const

theorem nextRow_weight_measurable_varying
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) (t : ℕ) (ht : t < T)
    (q : A → Meta) (hq : Measurable q) (a : A → Fin t → ι) (ha : Measurable a)
    (i : ι) : Measurable (fun z ↦ nextRow (μ z) t ht (q z) (a z) i) := by
  have has : Measurable (fun z : A ↦ (Fin.snoc (a z) i : Fin (t+1) → ι)) := by
    apply Measurable.of_eval
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa only [Fin.snoc_last] using (measurable_const : Measurable (fun _ : A ↦ i))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply k).comp ha
  simp_rw [nextRow_apply]
  exact Measurable.ite
    (measurableSet_lt measurable_const (prefixMass_measurable_varying μ hμ t (by omega) q hq a ha))
    ((prefixMass_measurable_varying μ hμ (t+1) (by omega) q hq (fun z ↦ Fin.snoc (a z) i) has).div
      (prefixMass_measurable_varying μ hμ t (by omega) q hq a ha)) measurable_const

def firstKernel (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) (hT : 0 < T) : Kernel A (Meta × ι) :=
  ProbabilityVector.kernel (fun z ↦ firstRow (μ z) hT) (firstRow_weight_measurable μ hμ hT)

instance firstKernel_markov (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) (hT : 0 < T) :
    IsMarkovKernel (firstKernel μ hμ hT) := by
  unfold firstKernel
  infer_instance

def nextKernel (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) : Kernel A ι :=
  ProbabilityVector.kernel (fun z ↦ nextRow (μ z) t ht q a)
    (nextRow_weight_measurable μ hμ t ht q a)

instance nextKernel_markov (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) :
    IsMarkovKernel (nextKernel μ hμ t ht q a) := by
  unfold nextKernel
  infer_instance

end Measurability
end
end Tournament.ConditionalRows
