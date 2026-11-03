module

public import Tournament.Graphs.FewObserverSampling
public import Tournament.Probability.BinomialBounds

@[expose] public section

namespace Tournament.ObserverSampling

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators unitInterval
noncomputable section

local instance : NormedSpace ℝ ℝ := @NormedField.toNormedSpace ℝ Real.normedField

variable {ι : Type*} [Fintype ι]

theorem expected_sample_card (W : Finset ι) (p : unitInterval) :
    (∫ S, ((sample W S).card:ℝ) ∂sampleLaw W p)=(p:ℝ)*(W.card:ℝ) := by
  change (∫ S, ((W.filter (fun v ↦ v∈S)).card:ℝ) ∂sampleLaw W p)=_
  rw [Tournament.Probability.integral_card_filter (sampleLaw W p) W (fun S v ↦ v∈S)]
  calc
    _ = ∑ _v∈W, (p:ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [sample,Finset.mem_filter,hv,true_and] using member_probability W p v hv
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem expected_heavy_cost_le (E : ι → ι → Prop) (W : Finset ι) (p : unitInterval) (k : ℕ)
    (hNq : ∀ a, ((observedMembers E W a).card:ℝ)*(p:ℝ)≤1/4) :
    (∫ S, ∑ a, if k≤(observedMembers E (sample W S) a).card then
      ((observedMembers E (sample W S) a).card:ℝ) else 0 ∂sampleLaw W p)≤
      (Fintype.card ι:ℝ)*(4/3:ℝ)*(1/4:ℝ)^k := by
  rw [integral_finsetSum Finset.univ (fun _ _ ↦ Integrable.of_finite)]
  calc
    _ ≤ ∑ _a : ι, (4/3:ℝ)*(1/4:ℝ)^k := by
      apply Finset.sum_le_sum
      intro a _
      exact Tournament.Probability.integral_binomial_tail (sampleLaw W p)
        (fun S ↦ (observedMembers E (sample W S) a).card) (observedMembers E W a).card k
        (fun S ↦ Finset.card_le_card (observedMembers_mono E (sample_subset W S) a))
        p p.2.1 p.2.2 (hNq a) (observed_count_probability E W a p)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

omit [Fintype ι] in
theorem sampled_edges_eq_filter (E : ι → ι → Prop) (W : Finset ι) (S : Set ι) :
    orderedEdges E (sample W S)=(orderedEdges E W).filter (fun e ↦ e.1∈S ∧ e.2∈S) := by
  ext e
  simp only [orderedEdges,sample,Finset.mem_filter,Finset.mem_offDiag]
  tauto

theorem expected_sampled_edges (E : ι → ι → Prop) (W : Finset ι) (p : unitInterval) :
    (∫ S, ((orderedEdges E (sample W S)).card:ℝ) ∂sampleLaw W p)=
      (p:ℝ)^2*((orderedEdges E W).card:ℝ) := by
  calc
    _ = ∫ S, (((orderedEdges E W).filter (fun e ↦ e.1∈S ∧ e.2∈S)).card:ℝ)
        ∂sampleLaw W p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun S ↦ congrArg (fun X : Finset (ι×ι) ↦ (X.card:ℝ))
        (sampled_edges_eq_filter E W S))
    _ = ∑ e∈orderedEdges E W, (sampleLaw W p).real {S | e.1∈S ∧ e.2∈S} := by
      convert Tournament.Probability.integral_card_filter (sampleLaw W p) (orderedEdges E W) (fun S e ↦ e.1∈S ∧ e.2∈S) using 1
      apply integral_congr_ae
      filter_upwards [] with S
      apply congrArg (fun X : Finset (ι×ι) ↦ (X.card:ℝ))
      ext e
      simp only [Finset.mem_filter]
    _ = ∑ _e∈orderedEdges E W, (p:ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro e he
      have h := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
      simpa only [sample,Finset.mem_filter,h.1,h.2.1,true_and] using pair_probability W p e.1 e.2 h.1 h.2.1 h.2.2
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

omit [Fintype ι] in
theorem orderedEdges_card_le_sum (E : ι → ι → Prop) (W : Finset ι) :
    (orderedEdges E W).card≤∑ u∈W, (observedMembers E W u).card := by
  have hSub : orderedEdges E W ⊆ W.biUnion (fun u ↦ (observedMembers E W u).image (fun v ↦ (u,v))) := by
    intro e he
    have hm := Finset.mem_filter.mp he
    have h := Finset.mem_offDiag.mp hm.1
    exact Finset.mem_biUnion.mpr ⟨e.1,h.1,Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨h.2.1,hm.2⟩,Prod.mk.eta⟩⟩
  exact (Finset.card_le_card hSub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun _ _ ↦ Finset.card_image_le)))

omit [Fintype ι] in
theorem orderedEdges_card_thin (E : ι → ι → Prop) (W : Finset ι) (f : ℝ)
    (hThin : ∀ a, ((observedMembers E W a).card:ℝ)≤f*(W.card:ℝ)) :
    ((orderedEdges E W).card:ℝ)≤(W.card:ℝ)*f*(W.card:ℝ) := by
  have hNat := orderedEdges_card_le_sum E W
  have hCast : ((orderedEdges E W).card:ℝ)≤∑ u∈W, ((observedMembers E W u).card:ℝ) := by exact_mod_cast hNat
  calc
    _ ≤ ∑ _u∈W, f*(W.card:ℝ) := hCast.trans (Finset.sum_le_sum (fun u _ ↦ hThin u))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem expected_survivors_ge (E : ι → ι → Prop) (W : Finset ι) (p : unitInterval) (k : ℕ) (f : ℝ)
    (hThin : ∀ a, ((observedMembers E W a).card:ℝ)≤f*(W.card:ℝ))
    (hNq : ∀ a, ((observedMembers E W a).card:ℝ)*(p:ℝ)≤1/4) :
    (p:ℝ)*(W.card:ℝ)-(Fintype.card ι:ℝ)*(4/3:ℝ)*(1/4:ℝ)^k-
        (p:ℝ)^2*(W.card:ℝ)*f*(W.card:ℝ)≤
      (∫ S, ((survivors E k (sample W S)).card:ℝ) ∂sampleLaw W p) := by
  have hDet (S : Set ι) : ((sample W S).card:ℝ)≤((survivors E k (sample W S)).card:ℝ)+
      (∑ a, if k≤(observedMembers E (sample W S) a).card then ((observedMembers E (sample W S) a).card:ℝ) else 0)+
        ((orderedEdges E (sample W S)).card:ℝ) := by exact_mod_cast deletion_card_bound E k (sample W S)
  have hInt := integral_mono (μ := sampleLaw W p) (Integrable.of_finite) (Integrable.of_finite) hDet
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite),
    expected_sample_card W p,expected_sampled_edges E W p] at hInt
  have hHeavy := expected_heavy_cost_le E W p k hNq
  have hEdge := mul_le_mul_of_nonneg_left (orderedEdges_card_thin E W f hThin) (sq_nonneg (p:ℝ))
  nlinarith

end
end Tournament.ObserverSampling
