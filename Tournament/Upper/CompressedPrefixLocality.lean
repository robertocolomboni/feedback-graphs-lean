module

public import Tournament.Upper.ExecutionPrefixLocality
public import Tournament.Probability.ConditionalRows
public import Tournament.Probability.FiniteReindex
public import Tournament.Model.ObservedCompletion

@[expose] public section

namespace Tournament.Model.FeedbackEW

open scoped BigOperators Classical
open Upper ConditionalRows

noncomputable section

variable {ι : Type*} {m : ℕ}

theorem takePrefix_trace_iff (default : ι) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B) (a x : ExecutionHistory ι m n B) :
    takePrefix t ht (executionTraceEquiv (ι := ι) m n B x) =
      takePrefix t ht (executionTraceEquiv (ι := ι) m n B a) ↔
      metadataPrefixEvent default n B t a x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hm := congrArg (fun z : metadataHistory m n B × (Fin t → ι) ↦ z.1) h
      exact hm
    · intro s hs
      have hh := congrFun (congrArg Prod.snd h) (⟨s,hs⟩ : Fin t)
      simpa only [takePrefix, executionTrace_eq_actions default, Fin.val_castLE,
        executionPath] using hh
  · rintro ⟨hm,ha⟩
    apply Prod.ext
    · exact hm
    · funext i
      simp only [takePrefix, executionTrace_eq_actions default, Fin.val_castLE]
      exact ha i.val i.isLt

def extendActions (default : ι) {t T : ℕ} (a : Fin t → ι) (i : Fin T) : ι :=
  if hi : i.val < t then a ⟨i.val,hi⟩ else default

theorem takePrefix_extendActions (default : ι) {t T : ℕ} (ht : t ≤ T)
    {Meta : Type*} (q : Meta) (a : Fin t → ι) :
    takePrefix t ht (q, extendActions default a) = (q,a) := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [takePrefix, extendActions, Fin.val_castLE, dite_eq_left i.isLt]

variable [Fintype ι] [Nonempty ι]

def compressedLaw (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ) :
    ProbabilityVector (metadataHistory m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → ι)) :=
  ((P.algorithm F n loss).execution B).reindex (executionTraceEquiv (ι := ι) m n B)

theorem prefixMass_compressedLaw (P : FeedbackEW ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B) (a : ExecutionHistory ι m n B) :
    ConditionalRows.prefixMass (P.compressedLaw F loss n B) t ht
      (takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)).1
      (takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)).2 =
      P.executionPrefixMass default F loss n B t a := by
  have hm : ConditionalRows.prefixMass (P.compressedLaw F loss n B) t ht
        (takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)).1
        (takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)).2 =
      (P.compressedLaw F loss n B).mean (fun z ↦
        if takePrefix t ht z = takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)
          then 1 else 0) := by
    simp only [ConditionalRows.prefixMass, FiniteConditional.fiberMass,
      ProbabilityVector.mean, mul_ite, mul_one, mul_zero, Prod.eta]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : takePrefix t ht x = takePrefix t ht (executionTraceEquiv (ι := ι) m n B a)
    · simp only [hx, ite_true]
    · simp only [hx, ite_false]
  rw [hm, compressedLaw, ProbabilityVector.reindex_mean]
  simp only [takePrefix_trace_iff default, executionPrefixMass]

theorem compressed_prefixMass_eq_of_observations (P : FeedbackEW ι m)
    (hMeta : P.MetadataIndependent) (default : ι) (F : ι → ι → Prop)
    (loss loss' : ℕ → ι → ℝ) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b+1) B)
    (q : metadataHistory m n B) (a : Fin t → ι)
    (hobs : ∀ s : Fin t, s.val+1 < t →
      comparisonObservation F (a s) (loss s.val) = comparisonObservation F (a s) (loss' s.val)) :
    ConditionalRows.prefixMass (P.compressedLaw F loss n B) t ht q a =
      ConditionalRows.prefixMass (P.compressedLaw F loss' n B) t ht q a := by
  let y := (executionTraceEquiv (ι := ι) m n B).symm (q,extendActions default a)
  have he : executionTraceEquiv (ι := ι) m n B y = (q,extendActions default a) :=
    Equiv.apply_symm_apply _ _
  have hp : takePrefix t ht (executionTraceEquiv (ι := ι) m n B y) = (q,a) := by
    rw [he]
    exact takePrefix_extendActions default ht q a
  have hpath (s : Fin t) : executionPath default n B y s.val = a s := by
    have htrace := executionTrace_eq_actions default m n B y (s.castLE ht)
    rw [he] at htrace
    simpa only [extendActions, Fin.val_castLE, dite_eq_left s.isLt, executionPath] using htrace.symm
  have hloc := P.executionPrefixMass_eq_of_observations hMeta default F loss loss' n B t ht y (by
    intro s hs
    have hst : s < t := by omega
    rw [hpath ⟨s,hst⟩]
    exact hobs ⟨s,hst⟩ hs)
  have hleft := P.prefixMass_compressedLaw default F loss n B t ht y
  have hright := P.prefixMass_compressedLaw default F loss' n B t ht y
  rw [hp] at hleft hright
  exact hleft.trans (hloc.trans hright.symm)

end
end Tournament.Model.FeedbackEW
