module

public import Tournament.Lower.DyadicSwitches
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance

@[expose] public section

namespace Tournament.Lower.Dyadic

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

def incrementSet (T t : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun j ↦ j.val+1∈ancestors t)

theorem incrementSet_zero (T : ℕ) : incrementSet T 0=∅ := by
  simp [incrementSet,ancestors]

theorem incrementSet_parent (T t : ℕ) (ht : 0<t) (htT : t≤T) :
    incrementSet T t=insert ⟨t-1,by omega⟩ (incrementSet T (parent t)) := by
  ext j
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  rw [ancestors,dite_eq_right (Nat.ne_of_gt ht),List.mem_cons]
  have heq : j.val+1=t ↔ j=⟨t-1,by omega⟩ := by
    constructor
    · intro h
      apply Fin.ext
      simp only
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
  rw [heq]

theorem new_increment_not_mem (T t : ℕ) (ht : 0<t) (htT : t≤T) :
    (⟨t-1,by omega⟩ : Fin T)∉incrementSet T (parent t) := by
  intro hmem
  have h : t∈ancestors (parent t) := by
    have := (Finset.mem_filter.mp hmem).2
    simpa only [Nat.sub_add_cancel (by omega : 1≤t)] using this
  have hb := mem_ancestors_bounds (parent t) t h
  have hp := parent_lt t ht
  omega

theorem incrementSet_card_le (T t : ℕ) : (incrementSet T t).card≤(ancestors t).length := by
  calc
    _ ≤ (ancestors t).toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun j : Fin T ↦ j.val+1)
      · intro j hj
        exact List.mem_toFinset.mpr ((Finset.mem_filter.mp hj).2)
      · intro j _ k _ hjk
        apply Fin.ext
        change j.val+1=k.val+1 at hjk
        omega
    _ = _ := List.toFinset_card_of_nodup (ancestors_nodup t)

def finiteWalk {Ω : Type*} {T : ℕ} (X : Fin T → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ j∈incrementSet T t, X j ω

theorem finiteWalk_zero {Ω : Type*} {T : ℕ} (X : Fin T → Ω → ℝ) : finiteWalk X 0=0 := by
  funext ω
  simp [finiteWalk,incrementSet_zero]

theorem finiteWalk_parent {Ω : Type*} {T : ℕ} (X : Fin T → Ω → ℝ)
    (t : ℕ) (ht : 0<t) (htT : t≤T) :
    finiteWalk X t=finiteWalk X (parent t)+X ⟨t-1,by omega⟩ := by
  funext ω
  simp only [finiteWalk,Pi.add_apply,incrementSet_parent T t ht htT,
    Finset.sum_insert (new_increment_not_mem T t ht htT)]
  ring

theorem finiteWalk_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℕ} (X : Fin T → Ω → ℝ) (hX : ∀ j, MemLp (X j) 2 μ)
    (hIndep : iIndepFun X μ) (v : ℝ) (hVar : ∀ j, Var[X j;μ]=v) (t : ℕ) :
    Var[finiteWalk X t;μ]=((incrementSet T t).card:ℝ)*v := by
  have hs := IndepFun.variance_sum (s := incrementSet T t)
    (fun j _ ↦ hX j) (fun _ _ _ _ hij ↦ hIndep.indepFun hij)
  have heq : (∑ j∈incrementSet T t, X j)=finiteWalk X t := by
    funext ω
    simp only [finiteWalk,Finset.sum_apply]
  rw [heq] at hs
  simpa only [hVar,Finset.sum_const,nsmul_eq_mul] using hs

theorem gaussian_increment_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : MemLp X 2 μ := by
  have hm : MemLp id 2 (μ.map X) := by
    rw [hX.map_eq]
    exact memLp_id_gaussianReal 2
  exact hm.comp_of_map hX.aemeasurable

theorem gaussian_walk_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℕ} (X : Fin T → Ω → ℝ) {v : ℝ≥0}
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 v) μ) (hIndep : iIndepFun X μ)
    (t : ℕ) (hT : 0<T) (htT : t≤T) :
    Var[finiteWalk X t;μ]≤upsilon T*(v:ℝ) := by
  rw [finiteWalk_variance X (fun j ↦ gaussian_increment_memLp (hLaw j)) hIndep (v:ℝ)
    (fun j ↦ (hLaw j).variance_eq.trans variance_id_gaussianReal)]
  exact mul_le_mul_of_nonneg_right
    (le_trans (by exact_mod_cast incrementSet_card_le T t) (ancestor_depth T t hT htT)) v.coe_nonneg

end
end Tournament.Lower.Dyadic
