module

public import Tournament.Upper.ExplorationPrivateSeed
public import Tournament.Graphs.Domination

@[expose] public section

namespace Tournament.Upper.Exploration

open Model.MeasurableGame
open scoped Classical
noncomputable section

theorem exploration_constant_cube : ((3:ℝ)^((4:ℝ)/3))^3=81 := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  norm_num

theorem exploration_constant_ge_one : (1:ℝ)≤(3:ℝ)^((4:ℝ)/3) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

theorem exploration_constant_lt_five : (3:ℝ)^((4:ℝ)/3)<5 := by
  by_contra h
  have hh : (5:ℝ)≤(3:ℝ)^((4:ℝ)/3) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5) hh 3
  rw [exploration_constant_cube] at hp
  norm_num at hp

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem observing_set_minimax_upper (E : ι → ι → Prop) (D : Finset ι) (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T) (default : ι) :
    minimax.{u,0} T E≤min
      ((3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3))
      (T:ℝ) := by
  apply le_min _ (minimax_le_horizon T E)
  have hD0 : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (observingSet_nonempty hD)
  have hL : 0<Real.log (Fintype.card ι:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1<Fintype.card ι))
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  let : Nonempty D := Set.nonempty_coe_sort.mpr (observingSet_nonempty hD)
  by_cases hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2
  · exact observable_graph_small_rate_minimax E D hD hK T hT hRate default
  · have hLarge := large_rate_fixed_action _ _ _ hD0 hL hT0 (lt_of_not_ge hRate)
    apply (minimax_le_horizon T E).trans
    apply hLarge.trans
    have hScale : 0≤((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by positivity
    have h := mul_le_mul_of_nonneg_right exploration_constant_ge_one hScale
    simpa only [one_mul,mul_assoc] using h

theorem observable_minimax_upper_sharp (E : ι → ι → Prop) (hObs : Observable E)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T) (default : ι) :
    minimax.{u,0} T E≤min
      ((3:ℝ)^((4:ℝ)/3)*((dominationNumber E hObs:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*
        (T:ℝ)^((2:ℝ)/3)) (T:ℝ) := by
  obtain ⟨D,hD,hCard⟩ := exists_minimum_observing E hObs
  simpa only [hCard] using observing_set_minimax_upper E D hD hK T hT default

theorem observable_minimax_upper (E : ι → ι → Prop) (hObs : Observable E)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T) (default : ι) :
    minimax.{u,0} T E≤min
      (5*((dominationNumber E hObs:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ) := by
  apply (observable_minimax_upper_sharp E hObs hK T hT default).trans
  apply min_le_min _ le_rfl
  have hScale : 0≤((dominationNumber E hObs:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*
      (T:ℝ)^((2:ℝ)/3) := by
    apply mul_nonneg
    · apply Real.rpow_nonneg
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1≤Fintype.card ι)))
    · positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right exploration_constant_lt_five.le hScale

end
end Tournament.Upper.Exploration
