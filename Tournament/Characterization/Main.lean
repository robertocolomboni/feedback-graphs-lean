module

public import Tournament.Characterization.Ratio
public import Tournament.Upper.SteeringMinimax
public import Tournament.Lower.FairExpertExpected
public import Tournament.Lower.Unobservable

@[expose] public section

namespace Tournament.Characterization

open Model.MeasurableGame
open scoped Classical
noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem strongly_revealing (E : ι → ι → Prop) (hE : StronglyRevealing E)
    (hK : 2 ≤ Fintype.card ι) (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt (T:ℝ)/4 ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤
        (2:ℝ)^40*Real.sqrt ((T:ℝ)*Real.log (Fintype.card ι:ℝ))*
          (Real.log (Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ)))^2 := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact ⟨Lower.FairExperts.minimax_lower_bound T (by omega) E hK,
    Upper.stronglyRevealing_minimax_upper_explicit E hE T (by omega)⟩

theorem characterization (E : ι → ι → Prop) (hK : 2 ≤ Fintype.card ι)
    (T : ℕ) (hT : 2 ≤ T) :
    (StronglyRevealing E →
      Real.sqrt (T:ℝ)/4 ≤ minimax.{u,0} T E ∧
        minimax.{u,0} T E ≤
          (2:ℝ)^40*Real.sqrt ((T:ℝ)*Real.log (Fintype.card ι:ℝ))*
            (Real.log (Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ)))^2) ∧
    (∀ hObs : Observable E, ¬StronglyRevealing E →
      (T:ℝ)^((2:ℝ)/3)*
          (max 1 (min (dominationNumber E hObs:ℝ) (T:ℝ)/
            (Real.log (Real.exp 1*(Fintype.card ι:ℝ)))^2))^((1:ℝ)/3)/
          (1024*(Real.log (2*(T:ℝ))/Real.log 2)) ≤ minimax.{u,0} T E ∧
        minimax.{u,0} T E ≤ min
          (5*((dominationNumber E hObs:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*
            (T:ℝ)^((2:ℝ)/3)) (T:ℝ)) ∧
    (¬Observable E → (T:ℝ)/4 ≤ minimax.{u,0} T E ∧ minimax.{u,0} T E ≤ (T:ℝ)) := by
  exact ⟨fun hE ↦ strongly_revealing E hE hK T hT,
    fun hObs hNot ↦ observable_nonrevealing E hObs hNot hK T hT,
    fun hNot ↦ Lower.Unobservable.minimax_bounds T E hNot hK⟩

end
end Tournament.Characterization
