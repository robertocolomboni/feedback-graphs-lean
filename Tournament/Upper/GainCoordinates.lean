module

public import Tournament.Upper.Coordinates
public import Tournament.Upper.BlockGain

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FiniteKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem probingPair_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (loss : ℕ → ι → ℝ) (t u : ℕ) (htu : t<u) :
    probingPair (H.kernel τ hτ) H.sampling loss t u =
      ∑ n, energyWeight τ (H.eigenvalue n)*(eigenMultiplier τ (H.eigenvalue n))^(u-t)*
        H.coordinate (loss t) n*H.coordinate (loss u) n := by
  let P := H.kernel τ hτ
  let k := u-t-1
  let v := ((P.act)^[k]) (loss u)
  have hm := P.stationary_mean_act H.sampling (H.kernel_stationary hτ) v
  change weightedInner H.sampling (loss t) (fun i ↦ v i-P.act v i)=_
  rw [weightedInner_sub,H.inner_coordinates,H.inner_coordinates,hm]
  calc
    _ = ∑ n, (H.coordinate (loss t) n*H.coordinate v n-
        H.coordinate (loss t) n*H.coordinate (P.act v) n) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      have hv : H.coordinate v n=(eigenMultiplier τ (H.eigenvalue n))^k*H.coordinate (loss u) n :=
        H.kernel_iterate_coordinate hτ k (loss u) n
      have hPv : H.coordinate (P.act v) n=(eigenMultiplier τ (H.eigenvalue n))^(k+1)*H.coordinate (loss u) n := by
        change H.coordinate (P.act (((P.act)^[k]) (loss u))) n=_
        rw [← Function.iterate_succ_apply' P.act k (loss u)]
        exact H.kernel_iterate_coordinate hτ (k+1) (loss u) n
      rw [hv,hPv]
      have hd : k+1=u-t := by dsimp only [k]; omega
      rw [← hd,pow_succ]
      calc
        _ = (1-eigenMultiplier τ (H.eigenvalue n))*(eigenMultiplier τ (H.eigenvalue n))^k*
            H.coordinate (loss t) n*H.coordinate (loss u) n := by ring
        _ = _ := by
          rw [one_sub_eigenMultiplier_eq (le_of_lt hτ) (by have := (H.eigenvalue_bounds n).1; linarith)]
          ring

theorem weighted_probingPair_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (loss : ℕ → ι → ℝ) (t u : ℕ) (htu : t<u) :
    (1-τ)^(u-t)*probingPair (H.kernel τ hτ) H.sampling loss t u =
      ∑ n, energyWeight τ (H.eigenvalue n)*(spectralCorrelation τ (H.eigenvalue n))^(u-t)*
        H.coordinate (loss t) n*H.coordinate (loss u) n := by
  rw [probingPair_coordinates H hτ loss t u htu,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  change (1-τ)^(u-t)*(energyWeight τ (H.eigenvalue n)*(eigenMultiplier τ (H.eigenvalue n))^(u-t)*
    H.coordinate (loss t) n*H.coordinate (loss u) n) =
      energyWeight τ (H.eigenvalue n)*((1-τ)*eigenMultiplier τ (H.eigenvalue n))^(u-t)*
        H.coordinate (loss t) n*H.coordinate (loss u) n
  rw [mul_pow]
  ring

def spectralGain (H : HoldingFamily ι) (τ : ℝ) (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  ∑ n, energyWeight τ (H.eigenvalue n)*
    (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
      if t<u then (spectralCorrelation τ (H.eigenvalue n))^(u-t)*
        H.coordinate (loss (offset+t)) n*H.coordinate (loss (offset+u)) n else 0)

theorem fixedRateGain_coordinates (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) :
    fixedRateProbingGain (H.kernel τ hτ) H.sampling loss τ offset h = spectralGain H τ loss offset h := by
  have hpair : ∀ t u, (if t<u then (1-τ)^(u-t)*probingPair (H.kernel τ hτ) H.sampling loss (offset+t) (offset+u) else 0) =
      ∑ n, energyWeight τ (H.eigenvalue n)*
        (if t<u then (spectralCorrelation τ (H.eigenvalue n))^(u-t)*
          H.coordinate (loss (offset+t)) n*H.coordinate (loss (offset+u)) n else 0) := by
    intro t u
    by_cases htu : t<u
    · simp only [ite_eq_left htu]
      have hp := weighted_probingPair_coordinates H hτ loss (offset+t) (offset+u) (by omega)
      have hd : (offset+u)-(offset+t)=u-t := by omega
      rw [hd] at hp
      rw [hp]
      apply Finset.sum_congr rfl
      intro n _
      ring
    · simp only [ite_eq_right htu,mul_zero,Finset.sum_const_zero]
  unfold fixedRateProbingGain spectralGain
  simp_rw [hpair]
  calc
    _ = ∑ t ∈ Finset.range h, ∑ n, ∑ u ∈ Finset.range h,
        energyWeight τ (H.eigenvalue n)*(if t<u then (spectralCorrelation τ (H.eigenvalue n))^(u-t)*
          H.coordinate (loss (offset+t)) n*H.coordinate (loss (offset+u)) n else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = ∑ n, ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
        energyWeight τ (H.eigenvalue n)*(if t<u then (spectralCorrelation τ (H.eigenvalue n))^(u-t)*
          H.coordinate (loss (offset+t)) n*H.coordinate (loss (offset+u)) n else 0) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end
end Tournament.Upper
