module

public import Tournament.Probability.TemporalDomination
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

namespace Tournament.GeometricPartition

open scoped BigOperators Classical

noncomputable section

theorem quadratic_zero_input (χ : ℝ) (offset h : ℕ) :
    quadratic χ (fun _ ↦ 0) offset h=0 := by simp [quadratic]

variable {β : Type*} [Fintype β]

theorem chunkSquareSum_sum_le_card (f : β → ℕ → ℝ) (offset : ℕ) (ns : List ℕ) :
    Restarts.chunkSquareSum (fun t ↦ ∑ b, f b t) offset ns≤
      (Fintype.card β:ℝ)*(∑ b, Restarts.chunkSquareSum (f b) offset ns) := by
  have hinterval : ∀ start n, (∑ t ∈ Finset.range (n+1), ∑ b, f b (start+t))^2≤
      (Fintype.card β:ℝ)*(∑ b, (∑ t ∈ Finset.range (n+1), f b (start+t))^2) := by
    intro start n
    rw [Finset.sum_comm]
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b ↦ ∑ t ∈ Finset.range (n+1), f b (start+t)))
  change Restarts.chunkSum _ offset ns≤_
  calc
    _ ≤ Restarts.chunkSum (fun start n ↦ (Fintype.card β:ℝ)*
        (∑ b, (∑ t ∈ Finset.range (n+1), f b (start+t))^2)) offset ns :=
      Restarts.chunkSum_mono _ _ hinterval ns offset
    _ = _ := by
      rw [Restarts.chunkSum_const_mul,Restarts.chunkSum_finset_sum]
      rfl

theorem quadratic_sum_le_card {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1)
    (f : β → ℕ → ℝ) (offset h : ℕ) :
    quadratic χ (fun t ↦ ∑ b, f b t) offset h≤
      (Fintype.card β:ℝ)*(∑ b, quadratic χ (f b) offset h) := by
  cases h with
  | zero => simp [quadratic]
  | succ n =>
    let μ := Restarts.law (1-χ) (sub_nonneg.mpr hχ1) (by linarith) n
    have hrepr (y : ℕ → ℝ) : quadratic χ y offset (n+1)=
        μ.mean (fun coins ↦ Restarts.chunkSquareSum y offset (Restarts.parts n coins)) :=
      quadratic_eq_mean_chunkSquares hχ hχ1 y offset n
    simp_rw [hrepr]
    calc
      _ ≤ μ.mean (fun coins ↦ (Fintype.card β:ℝ)*
          (∑ b, Restarts.chunkSquareSum (f b) offset (Restarts.parts n coins))) :=
        μ.mean_mono (fun coins ↦ chunkSquareSum_sum_le_card f offset (Restarts.parts n coins))
      _ = _ := by rw [ProbabilityVector.mean_const_mul,ProbabilityVector.mean_sum]

end
end Tournament.GeometricPartition
