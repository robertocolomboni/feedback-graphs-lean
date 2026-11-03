module

public import Tournament.Upper.ResetPrefixLocality
public import Tournament.Probability.DyadicTrajectoryEncoding

@[expose] public section

namespace Tournament.Model.RestartComparisonPolicy

open scoped BigOperators Classical
open Upper

noncomputable section

variable {ι : Type*} [Fintype ι] {m : ℕ}

def metadataWeight (π : RestartComparisonPolicy ι m) (n : ℕ)
    (q : Fin (m+1) × Restarts.Coins n) : ℝ :=
  π.rates q.1 * Restarts.law (π.restart q.1) (π.restart_nonneg q.1)
    (π.restart_le_one q.1) n q.2

def metadataPrefixMass (π : RestartComparisonPolicy ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (offset n t : ℕ)
    (a : DyadicBlockOutcome ι m n) : ℝ :=
  (π.law F loss offset n).mean (fun x ↦
    if (x.1, x.2.1) = (a.1, a.2.1) ∧
      SameActionPrefix t (blockActions default (Restarts.parts n x.2.1) x.2.2)
        (blockActions default (Restarts.parts n a.2.1) a.2.2) then 1 else 0)

theorem metadataPrefixMass_eq (π : RestartComparisonPolicy ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (offset n t : ℕ)
    (a : DyadicBlockOutcome ι m n) :
    π.metadataPrefixMass default F loss offset n t a =
      π.metadataWeight n (a.1,a.2.1) *
        (π.chunks a.1).prefixMass default F loss offset (Restarts.parts n a.2.1) t a.2.2 := by
  rcases a with ⟨j,coins,paths⟩
  unfold metadataPrefixMass law
  rw [ProbabilityVector.sigmaJoint_mean]
  simp_rw [ProbabilityVector.sigmaJoint_mean]
  simp [ProbabilityVector.mean, ResetComparisonPolicy.prefixMass,
    metadataWeight, Prod.mk.injEq, mul_ite, ite_and, Finset.mul_sum, mul_assoc]

theorem metadataPrefixMass_zero (π : RestartComparisonPolicy ι m) (default : ι)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (offset n : ℕ)
    (a : DyadicBlockOutcome ι m n) :
    π.metadataPrefixMass default F loss offset n 0 a = π.metadataWeight n (a.1,a.2.1) := by
  rw [metadataPrefixMass_eq, ResetComparisonPolicy.prefixMass_zero, mul_one]

theorem metadataPrefixMass_eq_of_observations (π : RestartComparisonPolicy ι m)
    (default : ι) (F : ι → ι → Prop) (loss loss' : ℕ → ι → ℝ)
    (offset n t : ℕ) (ht : t ≤ n+1) (a : DyadicBlockOutcome ι m n)
    (hobs : ∀ s, s+1 < t →
      comparisonObservation F (blockActions default (Restarts.parts n a.2.1) a.2.2 s)
        (loss (offset+s)) =
      comparisonObservation F (blockActions default (Restarts.parts n a.2.1) a.2.2 s)
        (loss' (offset+s))) :
    π.metadataPrefixMass default F loss offset n t a =
      π.metadataPrefixMass default F loss' offset n t a := by
  rw [metadataPrefixMass_eq, metadataPrefixMass_eq]
  congr 1
  apply ResetComparisonPolicy.prefixMass_eq_of_observations
  · simpa only [Restarts.parts_totalRounds] using ht
  · exact hobs

end
end Tournament.Model.RestartComparisonPolicy
