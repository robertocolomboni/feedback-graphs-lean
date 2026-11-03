module

public import Tournament.Upper.DartboardFreshDraws
public import Tournament.Graphs.Observing
public import Tournament.Model.GraphFeedback
public import Tournament.Upper.Scores

@[expose] public section

namespace Tournament.Upper.Exploration

open scoped Classical BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def law (D : Finset ι) [Nonempty D] (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) : ProbabilityVector (Bool × D) :=
  (Restarts.coin κ hκ hκ1).joint (fun _ ↦ ExponentialWeights.uniform)

def estimate (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (loss : ι → ℝ)
    (q : Bool × D) (i : ι) : ℝ :=
  if q.1 ∧ E q.2.val i then (D.card:ℝ)/(κ*(observingSources E D i).card)*loss i else 0

omit [Fintype ι] in
theorem uniform_observed (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (i : ι) (x : ℝ) :
    (ExponentialWeights.uniform (ι := D)).mean (fun s ↦ if E s.val i then x else 0)=
      ((observingSources E D i).card:ℝ)/(D.card:ℝ)*x := by
  change (∑ s : D, 1/(Fintype.card D:ℝ)*(if E s.val i then x else 0))=_
  simp only [Fintype.card_coe,mul_ite,mul_zero]
  rw [Finset.sum_coe_sort D (fun s : ι ↦ if E s i then 1/(D.card:ℝ)*x else 0),← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  unfold observingSources
  ring

omit [Fintype ι] in
theorem estimate_nonneg (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ι → ℝ) (hloss : ∀ i, 0≤loss i) (q : Bool × D) (i : ι) :
    0≤estimate E D κ loss q i := by
  unfold estimate
  split_ifs
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ (Nat.cast_nonneg _))) (hloss i)
  · exact le_rfl

omit [Fintype ι] in
theorem estimate_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (loss : ι → ℝ) (i : ι) :
    (law D κ hκ.le hκ1).mean (fun q ↦ estimate E D κ loss q i)=loss i := by
  rw [law,ProbabilityVector.joint_mean,Restarts.coin_mean]
  have ht : (fun s : D ↦ estimate E D κ loss (true,s) i)=
      (fun s : D ↦ if E s.val i then (D.card:ℝ)/(κ*(observingSources E D i).card)*loss i else 0) := by
    funext s
    simp only [estimate,true_and]
  have hf : (fun s : D ↦ estimate E D κ loss (false,s) i)=(fun _ ↦ (0:ℝ)) := by
    funext s
    simp only [estimate,Bool.false_eq_true,false_and,ite_false]
  rw [ht,hf,ProbabilityVector.mean_const,mul_zero,add_zero,uniform_observed]
  have hc : (observingSources E D i).card≠0 := Finset.card_ne_zero.mpr (observingSources_nonempty hD i)
  have hd : D.card≠0 := Finset.card_ne_zero.mpr (by rcases hD i with ⟨s,hs,_⟩; exact ⟨s,hs⟩)
  field_simp [ne_of_gt hκ,hc,hd]

omit [Fintype ι] in
theorem estimate_secondMoment (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (loss : ι → ℝ) (i : ι) :
    (law D κ hκ.le hκ1).mean (fun q ↦ (estimate E D κ loss q i)^2)=
      (D.card:ℝ)*(loss i)^2/(κ*(observingSources E D i).card) := by
  rw [law,ProbabilityVector.joint_mean,Restarts.coin_mean]
  have ht : (fun s : D ↦ (estimate E D κ loss (true,s) i)^2)=
      (fun s : D ↦ if E s.val i then ((D.card:ℝ)/(κ*(observingSources E D i).card)*loss i)^2 else 0) := by
    funext s
    by_cases h : E s.val i <;> simp [estimate,h]
  have hf : (fun s : D ↦ (estimate E D κ loss (false,s) i)^2)=(fun _ ↦ (0:ℝ)) := by
    funext s
    simp [estimate]
  rw [ht,hf,ProbabilityVector.mean_const,mul_zero,add_zero,uniform_observed]
  have hc : (observingSources E D i).card≠0 := Finset.card_ne_zero.mpr (observingSources_nonempty hD i)
  have hd : D.card≠0 := Finset.card_ne_zero.mpr (by rcases hD i with ⟨s,hs,_⟩; exact ⟨s,hs⟩)
  field_simp [ne_of_gt hκ,hc,hd]

omit [Fintype ι] in
theorem estimate_le (E : ι → ι → Prop) (D : Finset ι) (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (loss : ι → ℝ) (hloss : BoundedLoss loss) (q : Bool × D) (i : ι) :
    estimate E D κ loss q i≤(D.card:ℝ)/κ := by
  unfold estimate
  split_ifs
  · have hc : (1:ℝ)≤((observingSources E D i).card:ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (observingSources_nonempty hD i)
    have hd : κ≤κ*((observingSources E D i).card:ℝ) := by nlinarith
    exact (mul_le_of_le_one_right (by positivity) (hloss i).2).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hκ hd)
  · positivity

omit [Fintype ι] in
theorem estimate_observable (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ)
    (loss : ι → ℝ) (q : Bool × D) (arm i : ι) :
    estimate E D κ (Model.graphObservation E (if q.1 then q.2.val else arm) loss) q i=
      estimate E D κ loss q i := by
  rcases q with ⟨b,s⟩
  cases b <;> by_cases hi : E s.val i <;> simp [estimate,Model.graphObservation,hi]

omit [Fintype ι] in
theorem estimate_secondMoment_le (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (loss : ι → ℝ) (hloss : BoundedLoss loss) (i : ι) :
    (law D κ hκ.le hκ1).mean (fun q ↦ (estimate E D κ loss q i)^2)≤(D.card:ℝ)/κ := by
  rw [estimate_secondMoment E D hD κ hκ hκ1 loss i]
  have hc : (1:ℝ)≤((observingSources E D i).card:ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (observingSources_nonempty hD i)
  have hd : κ≤κ*((observingSources E D i).card:ℝ) := by nlinarith
  have hsq : (loss i)^2≤1 := by nlinarith [(hloss i).1,(hloss i).2]
  calc
    _ ≤ (D.card:ℝ)/(κ*(observingSources E D i).card) :=
      div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) D.card]) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hκ hd

theorem weighted_estimate_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (loss : ι → ℝ) (p : ProbabilityVector ι) :
    (law D κ hκ.le hκ1).mean (fun q ↦ p.mean (estimate E D κ loss q))=p.mean loss := by
  change (law D κ hκ.le hκ1).mean (fun q ↦ ∑ i, p i*estimate E D κ loss q i)=_
  rw [ProbabilityVector.mean_sum]
  simp_rw [ProbabilityVector.mean_const_mul,estimate_mean E D hD κ hκ hκ1 loss]
  rfl

theorem weighted_estimate_secondMoment_le (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (loss : ι → ℝ) (hloss : BoundedLoss loss) (p : ProbabilityVector ι) :
    (law D κ hκ.le hκ1).mean (fun q ↦ p.squareNorm (estimate E D κ loss q))≤(D.card:ℝ)/κ := by
  change (law D κ hκ.le hκ1).mean (fun q ↦ ∑ i, p i*(estimate E D κ loss q i)^2)≤_
  rw [ProbabilityVector.mean_sum]
  simp_rw [ProbabilityVector.mean_const_mul]
  calc
    _ ≤ ∑ i, p i*((D.card:ℝ)/κ) := Finset.sum_le_sum (fun i _ ↦
      mul_le_mul_of_nonneg_left (estimate_secondMoment_le E D hD κ hκ hκ1 loss hloss i) (p.nonneg i))
    _ = _ := p.mean_const _

end
end Tournament.Upper.Exploration
