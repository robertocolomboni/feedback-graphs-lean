module

public import Tournament.Lower.Domination
public import Tournament.Model.Minimax

@[expose] public section

namespace Tournament.Lower.Domination

open MeasureTheory Model.MeasurableGame
noncomputable section

universe u v
variable {ι : Type u} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable [Fintype ι] [Nonempty ι]

theorem minimax_lower_bound (T : ℕ) (hT : 2≤T) (E : ι → ι → Prop)
    (hObs : Observable E) (hNot : ¬StronglyRevealing E) (hK : 2≤Fintype.card ι) :
    bound (Fintype.card ι) (dominationNumber E hObs) T≤minimax.{u,v} T E := by
  apply le_minimax
  intro σ
  let := σ.seedSpace
  let := σ.probability
  obtain ⟨loss,hLoss,hLower⟩ := lower_bound σ.law T hT σ.learner E hObs hNot hK
  refine ⟨loss,hLoss,?_⟩
  simpa only [Strategy.regret] using hLower

theorem minimax_lower_bound_explicit (T : ℕ) (hT : 2≤T) (E : ι → ι → Prop)
    (hObs : Observable E) (hNot : ¬StronglyRevealing E) (hK : 2≤Fintype.card ι) :
    (T:ℝ)^((2:ℝ)/3)*
      (max 1 (min (dominationNumber E hObs:ℝ) (T:ℝ)/
        (Real.log (Real.exp 1*(Fintype.card ι:ℝ)))^2))^((1:ℝ)/3)/
      (1024*(Real.log (2*(T:ℝ))/Real.log 2))≤minimax.{u,v} T E := by
  simpa only [bound,logCard_eq (Fintype.card ι) hK,Dyadic.upsilon] using
    minimax_lower_bound.{u,v} T hT E hObs hNot hK

end
end Tournament.Lower.Domination
