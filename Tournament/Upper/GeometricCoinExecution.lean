module

public import Tournament.Upper.GeometricSwitches
public import Tournament.Probability.BernoulliCoins
public import Tournament.Probability.FiniteIndicators

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators unitInterval
noncomputable section

abbrev CoinSpace (T : ℕ) := Fin T → Bool

def coinPath {T : ℕ} (ω : CoinSpace T) (n : ℕ) : Bool := if hn : n<T then ω ⟨n,hn⟩ else false

def coinLaw (T : ℕ) (p : unitInterval) : Measure (CoinSpace T) :=
  Tournament.Probability.BernoulliCoins.productLaw (Fin T) p

instance coinLaw_probability (T : ℕ) (p : unitInterval) : IsProbabilityMeasure (coinLaw T p) := by
  unfold coinLaw
  infer_instance

theorem coinPath_fin {T : ℕ} (ω : CoinSpace T) (t : Fin T) : coinPath ω t.val=ω t := by
  simp only [coinPath,dite_eq_left t.isLt]

theorem state_reset_current {T : ℕ} (d : ℕ → ℝ) (t : Fin T) (ω : CoinSpace T) :
    state d (coinPath (Function.update ω t false)) t.val=state d (coinPath ω) t.val := by
  apply state_eq_of_past_coins
  intro n hn
  have hnT : n<T := hn.trans t.isLt
  have hne : (⟨n,hnT⟩ : Fin T)≠t := by
    intro h
    have hv := congrArg Fin.val h
    change n=t.val at hv
    omega
  simp only [coinPath,dite_eq_left hnT,Function.update_of_ne hne]

theorem start_probability {T : ℕ} (d : ℕ → ℝ) (p : unitInterval) (t : Fin T) :
    (coinLaw T p).real {ω | Starts d (coinPath ω) t.val}=
      (coinLaw T p).real {ω | (state d (coinPath ω) t.val).start=none}*(p:ℝ) := by
  let F : CoinSpace T → Bool := fun ω ↦ decide ((state d (coinPath ω) t.val).start=none)
  have hReset (ω : CoinSpace T) : F (Function.update ω t false)=F ω := by
    dsimp [F]
    rw [state_reset_current]
  have h := Tournament.Probability.BernoulliCoins.fresh_success_probability p t F hReset
  simpa only [F,Starts,coinPath_fin,decide_eq_true_eq,coinLaw] using h

def restCount (d : ℕ → ℝ) {T : ℕ} (ω : CoinSpace T) : ℕ :=
  ∑ t∈Finset.range T, if (state d (coinPath ω) t).start=none then 1 else 0

theorem restCount_le (d : ℕ → ℝ) {T : ℕ} (ω : CoinSpace T) : restCount d ω≤T := by
  calc
    _ ≤ ∑ _t∈Finset.range T, (1:ℕ) := Finset.sum_le_sum (fun _ _ ↦ by split_ifs <;> omega)
    _ = _ := by simp

theorem expected_probeCount_eq (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) :
    (∫ ω, (probeCount d (coinPath ω) T:ℝ) ∂coinLaw T p)=
      (p:ℝ)*(∫ ω, (restCount d ω:ℝ) ∂coinLaw T p) := by
  rw [show (fun ω : CoinSpace T ↦ (probeCount d (coinPath ω) T:ℝ))=
      fun ω ↦ ((∑ t∈Finset.range T, if Starts d (coinPath ω) t then 1 else 0 : ℕ):ℝ) from rfl]
  rw [Tournament.Probability.integral_nat_count (coinLaw T p) (Finset.range T)
    (fun ω t ↦ Starts d (coinPath ω) t)]
  change _=(p:ℝ)*(∫ ω, ((∑ t∈Finset.range T,
    if (state d (coinPath ω) t).start=none then 1 else 0 : ℕ):ℝ) ∂coinLaw T p)
  rw [Tournament.Probability.integral_nat_count (coinLaw T p) (Finset.range T)
    (fun ω t ↦ (state d (coinPath ω) t).start=none),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [start_probability d p ⟨t,Finset.mem_range.mp ht⟩]
  ring

theorem expected_probeCount_le (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) :
    (∫ ω, (probeCount d (coinPath ω) T:ℝ) ∂coinLaw T p)≤(p:ℝ)*(T:ℝ) := by
  rw [expected_probeCount_eq]
  have hRest := integral_mono (μ := coinLaw T p) Integrable.of_finite (integrable_const (T:ℝ))
    (fun ω ↦ (show (restCount d ω:ℝ)≤(T:ℝ) by exact_mod_cast restCount_le d ω))
  simp only [integral_const,probReal_univ,one_smul] at hRest
  exact mul_le_mul_of_nonneg_left hRest p.2.1

end
end Tournament.Upper.GeometricProbing
