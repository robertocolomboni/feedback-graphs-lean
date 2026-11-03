module

public import Tournament.Upper.ExplorationMinimax
public import Tournament.Lower.DominationMinimax

@[expose] public section

namespace Tournament.Characterization

open Model.MeasurableGame
noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem observable_nonrevealing (E : ι → ι → Prop) (hObs : Observable E) (hNot : ¬StronglyRevealing E)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 2≤T) :
    (T:ℝ)^((2:ℝ)/3)*
        (max 1 (min (dominationNumber E hObs:ℝ) (T:ℝ)/
          (Real.log (Real.exp 1*(Fintype.card ι:ℝ)))^2))^((1:ℝ)/3)/
        (1024*(Real.log (2*(T:ℝ))/Real.log 2))≤minimax.{u,0} T E ∧
      minimax.{u,0} T E≤min
        (5*((dominationNumber E hObs:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ) :=
  ⟨Lower.Domination.minimax_lower_bound_explicit T hT E hObs hNot hK,
    Upper.Exploration.observable_minimax_upper E hObs hK T (by omega) (Classical.arbitrary ι)⟩

end
end Tournament.Characterization
