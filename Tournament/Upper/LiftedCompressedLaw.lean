module

public import Tournament.Upper.CompressedPrefixLocality
public import Tournament.Model.ConditionalFeedback

@[expose] public section

universe u

namespace Tournament.Upper

open MeasureTheory
open scoped Classical

noncomputable section

abbrev SeedMetadata (m : ℕ) (n : ℕ → ℕ) (B : ℕ) : Type u :=
  ULift.{u} (metadataHistory m n B)

instance seedMetadataNonempty (m : ℕ) (n : ℕ → ℕ) (B : ℕ) :
    Nonempty (SeedMetadata.{u} m n B) := by
  have h : Nonempty (metadataHistory m n B) := by
    induction B with
    | zero => exact ⟨ULift.up ()⟩
    | succ B ih =>
      obtain ⟨q⟩ := ih
      obtain ⟨coins⟩ := (Restarts.law 0 (by norm_num) (by norm_num) (n B)).nonempty
      exact ⟨(q, (⟨0, Nat.zero_lt_succ m⟩, coins))⟩
  exact h.map ULift.up

instance seedMetadataMeasurableSpace (m : ℕ) (n : ℕ → ℕ) (B : ℕ) :
    MeasurableSpace (SeedMetadata.{u} m n B) := ⊤

instance seedMetadataDiscreteMeasurableSpace (m : ℕ) (n : ℕ → ℕ) (B : ℕ) :
    DiscreteMeasurableSpace (SeedMetadata.{u} m n B) := ⟨fun _ ↦ trivial⟩

end

end Tournament.Upper

namespace Tournament.Model.FeedbackEW

open Upper ConditionalRows
open scoped BigOperators Classical

noncomputable section

variable {ι : Type u} [Fintype ι] [Nonempty ι] {m : ℕ}

def liftedCompressedLaw (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ) :
    ProbabilityVector (SeedMetadata.{u} m n B ×
      (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι)) :=
  (P.compressedLaw F loss n B).reindex
    (Equiv.prodCongr Equiv.ulift.symm (Equiv.refl _))

@[simp] theorem liftedCompressedLaw_apply (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ)
    (x : SeedMetadata.{u} m n B × (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι)) :
    P.liftedCompressedLaw F loss n B x = P.compressedLaw F loss n B (x.1.down, x.2) := rfl

theorem liftedCompressedLaw_mean (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ)
    (f : SeedMetadata.{u} m n B × (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι) → ℝ) :
    (P.liftedCompressedLaw F loss n B).mean f =
      (P.compressedLaw F loss n B).mean (fun x ↦ f (ULift.up x.1, x.2)) :=
  ProbabilityVector.reindex_mean _ _ _

theorem liftedCompressedLaw_mean_execution (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B : ℕ)
    (f : SeedMetadata.{u} m n B × (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι) → ℝ) :
    (P.liftedCompressedLaw F loss n B).mean f =
      ((P.algorithm F n loss).execution B).mean (fun h ↦
        f (ULift.up (executionTraceEquiv (ι := ι) m n B h).1,
          (executionTraceEquiv (ι := ι) m n B h).2)) := by
  rw [liftedCompressedLaw_mean, compressedLaw, ProbabilityVector.reindex_mean]

theorem prefixMass_liftedCompressedLaw (P : FeedbackEW ι m) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ → ℕ) (B t : ℕ)
    (ht : t ≤ prefixHorizon (fun b ↦ n b + 1) B)
    (q : SeedMetadata.{u} m n B) (a : Fin t → ι) :
    prefixMass (P.liftedCompressedLaw F loss n B) t ht q a =
      prefixMass (P.compressedLaw F loss n B) t ht q.down a := by
  unfold prefixMass FiniteConditional.fiberMass
  let e : (SeedMetadata.{u} m n B × (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι)) ≃
      (metadataHistory m n B × (Fin (prefixHorizon (fun b ↦ n b + 1) B) → ι)) :=
    Equiv.prodCongr Equiv.ulift (Equiv.refl _)
  apply Fintype.sum_equiv e
  intro x
  rcases x with ⟨⟨q'⟩, b⟩
  rcases q with ⟨q⟩
  simp [takePrefix, e, liftedCompressedLaw, ProbabilityVector.reindex]

theorem liftedCompressedLaw_completionLocal [LinearOrder ι]
    (P : FeedbackEW ι m) (hMeta : P.MetadataIndependent) (default : ι)
    (E : ι → ι → Prop) (n : ℕ → ℕ) (B : ℕ) :
    ConditionalFeedback.CompletionLocal
      (fun loss ↦ P.liftedCompressedLaw (selectedEdge E) loss n B) E := by
  intro loss t ht q a i
  rw [prefixMass_liftedCompressedLaw, prefixMass_liftedCompressedLaw]
  apply P.compressed_prefixMass_eq_of_observations hMeta default (selectedEdge E)
  intro s hs
  let j : Fin t := ⟨s.val, by omega⟩
  have hsnoc : (Fin.snoc a i : Fin (t + 1) → ι) s = a j := by
    have hs' : s = j.castSucc := Fin.ext rfl
    rw [hs', Fin.snoc_castSucc]
  rw [hsnoc]
  exact observedCompletion_preserves_comparison E a loss j

end

end Tournament.Model.FeedbackEW
