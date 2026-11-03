module

public import Tournament.Foundations.Centering

@[expose] public section

namespace Tournament.ProbabilityVector

variable {Ω : Type*} [Fintype Ω]

@[ext] theorem ext_weights {μ ν : ProbabilityVector Ω} (h : ∀ ω, μ ω=ν ω) : μ=ν := by
  cases μ with
  | mk a ha hsum =>
    cases ν with
    | mk b hb hsum' =>
      have hab : a=b := funext h
      subst b
      rfl

end Tournament.ProbabilityVector
