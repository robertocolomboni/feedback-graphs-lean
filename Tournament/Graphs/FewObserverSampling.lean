module

public import Tournament.Graphs.FewObserverDeletion
public import Tournament.Probability.BernoulliSubsets
public import Mathlib.Tactic.Tauto

@[expose] public section

namespace Tournament.ObserverSampling

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval
noncomputable section

variable {ι : Type*} [Fintype ι]

def sample (W : Finset ι) (S : Set ι) : Finset ι := W.filter (fun v ↦ v∈S)

def sampleLaw (W : Finset ι) (p : unitInterval) : Measure (Set ι) := setBernoulli (W : Set ι) p

instance sampleLaw_probability (W : Finset ι) (p : unitInterval) : IsProbabilityMeasure (sampleLaw W p) := by
  unfold sampleLaw
  infer_instance

omit [Fintype ι] in
theorem sample_subset (W : Finset ι) (S : Set ι) : sample W S ⊆ W := Finset.filter_subset _ _

omit [Fintype ι] in
theorem observed_sample_set (E : ι → ι → Prop) (W : Finset ι) (a : ι) (S : Set ι) :
    (observedMembers E (sample W S) a : Set ι)=S∩(observedMembers E W a : Set ι) := by
  ext v
  simp only [observedMembers,sample,Finset.mem_coe,Finset.mem_filter,Set.mem_inter_iff]
  tauto

theorem observed_count_probability (E : ι → ι → Prop) (W : Finset ι) (a : ι)
    (p : unitInterval) (b : ℕ) :
    (sampleLaw W p).real {S | (observedMembers E (sample W S) a).card=b}=
      ((observedMembers E W a).card.choose b:ℝ)*(p:ℝ)^b*(1-(p:ℝ))^((observedMembers E W a).card-b) := by
  have hSub : (observedMembers E W a : Set ι) ⊆ (W : Set ι) := Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have hc (S : Set ι) : (observedMembers E (sample W S) a).card=(S∩(observedMembers E W a : Set ι)).ncard := by
    rw [← observed_sample_set,Set.ncard_coe_finset]
  simp_rw [hc]
  simpa only [sampleLaw,Set.inter_eq_right.mpr hSub,Set.ncard_coe_finset] using
    Tournament.Probability.intersection_count_probability (W : Set ι) (observedMembers E W a : Set ι) p b

omit [Fintype ι] in
theorem inter_singleton (S : Set ι) (v : ι) :
    S∩{v}=(if v∈S then ({v} : Set ι) else ∅) := by
  ext z
  by_cases hv : v∈S <;> simp_all

theorem member_probability (W : Finset ι) (p : unitInterval) (v : ι) (hv : v∈W) :
    (sampleLaw W p).real {S | v∈sample W S}=(p:ℝ) := by
  have hEvent : {S : Set ι | v∈sample W S}={S : Set ι | (S∩{v}).ncard=1} := by
    ext S
    change (v∈sample W S) ↔ (S∩{v}).ncard=1
    rw [inter_singleton]
    by_cases hs : v∈S <;> simp [sample,hv,hs]
  rw [hEvent]
  have hInter : (W : Set ι)∩{v}=({v} : Set ι) := by rw [inter_singleton]; simp only [Finset.mem_coe,hv,ite_true]
  simpa only [sampleLaw,hInter,Set.ncard_singleton,Nat.choose_self,Nat.cast_one,one_mul,pow_one,Nat.sub_self,pow_zero,mul_one] using
    Tournament.Probability.intersection_count_probability (W : Set ι) {v} p 1

omit [Fintype ι] in
theorem inter_pair (S : Set ι) (u v : ι) :
    S∩{u,v}=(if u∈S then ({u} : Set ι) else ∅)∪(if v∈S then ({v} : Set ι) else ∅) := by
  rw [← Set.singleton_union,Set.inter_union_distrib_left,inter_singleton,inter_singleton]

theorem pair_probability (W : Finset ι) (p : unitInterval) (u v : ι)
    (hu : u∈W) (hv : v∈W) (hne : u≠v) :
    (sampleLaw W p).real {S | u∈sample W S ∧ v∈sample W S}=(p:ℝ)^2 := by
  have hEvent : {S : Set ι | u∈sample W S ∧ v∈sample W S}={S : Set ι | (S∩{u,v}).ncard=2} := by
    ext S
    change (u∈sample W S ∧ v∈sample W S) ↔ (S∩{u,v}).ncard=2
    rw [inter_pair]
    by_cases hs : u∈S <;> by_cases ht : v∈S <;> simp [sample,hu,hv,hs,ht,Set.ncard_pair hne.symm]
  rw [hEvent]
  have hInter : (W : Set ι)∩{u,v}=({u,v} : Set ι) := by
    rw [inter_pair]
    simp only [Finset.mem_coe,hu,hv,ite_true,Set.singleton_union]
  simpa only [sampleLaw,hInter,Set.ncard_pair hne,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one] using
    Tournament.Probability.intersection_count_probability (W : Set ι) {u,v} p 2

end
end Tournament.ObserverSampling
