module

public import Tournament.Model.GraphFeedback
public import Tournament.Probability.PrefixConditioning

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical
open FinitePath

noncomputable section

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem recordComparisons_eq_of_observations (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ) (hist : History ι n)
    (hobs : ∀ t < n, comparisonObservation F (stateAt n hist t) (loss t) =
      comparisonObservation F (stateAt n hist t) (loss' t)) :
    recordComparisons F loss n hist = recordComparisons F loss' n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : ∀ t < n, comparisonObservation F (stateAt n hist.1 t) (loss t) =
        comparisonObservation F (stateAt n hist.1 t) (loss' t) := by
      intro t ht
      simpa only [stateAt_prefix n hist t (by omega)] using hobs t (by omega)
    have hlast := hobs n (by omega)
    rw [stateAt_prefix n hist n le_rfl, stateAt_last] at hlast
    change ((recordComparisons F loss n hist.1,
      comparisonObservation F (lastState n hist.1) (loss n)), hist.2) = _
    rw [ih hist.1 hpre, hlast]
    rfl

namespace ComparisonPolicy

theorem law_atom_eq_of_observations (π : ComparisonPolicy ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ) (hist : History ι n)
    (hobs : ∀ t < n, comparisonObservation F (stateAt n hist t) (loss t) =
      comparisonObservation F (stateAt n hist t) (loss' t)) :
    π.law F loss n hist = π.law F loss' n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : ∀ t < n, comparisonObservation F (stateAt n hist.1 t) (loss t) =
        comparisonObservation F (stateAt n hist.1 t) (loss' t) := by
      intro t ht
      simpa only [stateAt_prefix n hist t (by omega)] using hobs t (by omega)
    have hlast := hobs n (by omega)
    rw [stateAt_prefix n hist n le_rfl, stateAt_last] at hlast
    change π.law F loss n hist.1 *
      π.next n (recordComparisons F loss n hist.1)
        (comparisonObservation F (lastState n hist.1) (loss n)) hist.2 = _
    rw [ih hist.1 hpre, recordComparisons_eq_of_observations F loss loss' n hist.1 hpre,
      hlast]
    rfl

theorem mean_prefix (π : ComparisonPolicy ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n t : ℕ) (ht : t ≤ n) (f : History ι t → ℝ) :
    (π.law F loss n).mean (fun hist ↦ f (initialSegment n hist t ht)) =
      (π.law F loss t).mean f := by
  induction n with
  | zero =>
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    simp only [prefix_self]
  | succ n ih =>
    by_cases htn : t ≤ n
    · change ((π.law F loss n).joint (fun hist ↦
        π.next n (recordComparisons F loss n hist)
          (comparisonObservation F (lastState n hist) (loss n)))).mean _ = _
      simp_rw [prefix_succ_of_le n _ t htn]
      rw [ProbabilityVector.joint_first_mean (π.law F loss n)
        (fun hist ↦ π.next n (recordComparisons F loss n hist)
          (comparisonObservation F (lastState n hist) (loss n)))
        (fun hist ↦ f (initialSegment n hist t htn))]
      exact ih htn
    · have ht' : t = n+1 := by omega
      subst t
      simp only [prefix_self]

theorem prefixMass_eq (π : ComparisonPolicy ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n t : ℕ) (ht : t ≤ n) (a : History ι t) :
    FiniteConditional.fiberMass (π.law F loss n)
      (fun hist ↦ initialSegment n hist t ht) a = π.law F loss t a := by
  have h := π.mean_prefix F loss n t ht (fun x ↦ if x = a then 1 else 0)
  simpa [ProbabilityVector.mean, FiniteConditional.fiberMass, mul_ite] using h

theorem prefixMass_eq_of_observations (π : ComparisonPolicy ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n t : ℕ) (ht : t ≤ n) (a : History ι t)
    (hobs : ∀ s < t, comparisonObservation F (stateAt t a s) (loss s) =
      comparisonObservation F (stateAt t a s) (loss' s)) :
    FiniteConditional.fiberMass (π.law F loss n)
      (fun hist ↦ initialSegment n hist t ht) a =
    FiniteConditional.fiberMass (π.law F loss' n)
      (fun hist ↦ initialSegment n hist t ht) a := by
  rw [prefixMass_eq, prefixMass_eq]
  exact π.law_atom_eq_of_observations F loss loss' t a hobs

theorem law_atom_eq_of_graph_observations [LinearOrder ι]
    (π : ComparisonPolicy ι) (E : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ) (hist : History ι n)
    (hobs : ∀ t < n, graphObservation E (stateAt n hist t) (loss t) =
      graphObservation E (stateAt n hist t) (loss' t)) :
    π.law (selectedEdge E) loss n hist = π.law (selectedEdge E) loss' n hist := by
  apply π.law_atom_eq_of_observations
  intro t ht
  rw [← selectedComparison_record, ← selectedComparison_record, hobs t ht]

end ComparisonPolicy
end
end Tournament.Model
