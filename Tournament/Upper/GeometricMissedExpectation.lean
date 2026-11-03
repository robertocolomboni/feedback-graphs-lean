module

public import Tournament.Upper.GeometricCoinExecution
public import Tournament.Probability.OrderedGeometricTail

@[expose] public section

namespace Tournament.Upper.GeometricProbing

open MeasureTheory
open scoped Classical BigOperators unitInterval
noncomputable section

def terminalRounds (d : ℕ → ℝ) (T : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun t ↦ Terminal d T t.val)

def prefixTrials (d : ℕ → ℝ) {T : ℕ} (t : Fin T) : Finset (Fin T) :=
  (terminalRounds d T).filter (fun u ↦ u≤t)

theorem before_boundary_iff_avoid (d : ℕ → ℝ) {T : ℕ} (t : Fin T) (ω : CoinSpace T) :
    t.val<finalStart d (coinPath ω) T ↔ ∀ u∈prefixTrials d t, ω u=false := by
  constructor
  · intro hBefore u hu
    have hTerms := Finset.mem_filter.mp hu
    have hTerm := (Finset.mem_filter.mp hTerms.1).2
    have huNat : u.val≤t.val := hTerms.2
    simpa only [coinPath_fin] using terminal_coin_before_finalStart d (coinPath ω) T u.val (by omega) hTerm
  · intro hAvoid
    by_contra hBefore
    have hs : finalStart d (coinPath ω) T≤t.val := le_of_not_gt hBefore
    have hsT : finalStart d (coinPath ω) T<T := hs.trans_lt t.isLt
    have hSuccess := finalStart_success d (coinPath ω) T hsT
    let u : Fin T := ⟨finalStart d (coinPath ω) T,hsT⟩
    have hu : u∈prefixTrials d t := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u,hSuccess.1⟩,hs⟩
    have hFalse := hAvoid u hu
    have hTrue : ω u=true := (coinPath_fin ω u).symm.trans hSuccess.2
    rw [hFalse] at hTrue
    cases hTrue

theorem before_boundary_probability (d : ℕ → ℝ) {T : ℕ} (p : unitInterval) (t : Fin T) :
    (coinLaw T p).real {ω | t.val<finalStart d (coinPath ω) T}=
      (1-(p:ℝ))^(Tournament.Probability.inclusiveRank (terminalRounds d T) t) := by
  have hSet : {ω : CoinSpace T | t.val<finalStart d (coinPath ω) T}=
      {ω | ∀ u∈prefixTrials d t, ω u=false} := by
    ext ω
    exact before_boundary_iff_avoid d t ω
  rw [hSet]
  exact Tournament.Probability.BernoulliCoins.avoid_probability p (prefixTrials d t)

theorem missed_count_eq (d : ℕ → ℝ) {T : ℕ} (ω : CoinSpace T) :
    terminalCount d T (finalStart d (coinPath ω) T)=
      ∑ t : Fin T, if Terminal d T t.val ∧ t.val<finalStart d (coinPath ω) T then 1 else 0 := by
  let s := finalStart d (coinPath ω) T
  have hs : s≤T := finalStart_le_horizon d (coinPath ω) T
  have hSet : (Finset.range s).filter (Terminal d T)=
      (Finset.range T).filter (fun t ↦ Terminal d T t ∧ t<s) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨ht,hTerm⟩
      exact ⟨by omega,hTerm,ht⟩
    · rintro ⟨_,hTerm,ht⟩
      exact ⟨ht,hTerm⟩
  change ((Finset.range s).filter (Terminal d T)).card=_
  rw [hSet,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_range]

theorem expected_missed_count_eq (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) :
    (∫ ω, (terminalCount d T (finalStart d (coinPath ω) T):ℝ) ∂coinLaw T p)=
      ∑ t∈terminalRounds d T, (1-(p:ℝ))^(Tournament.Probability.inclusiveRank (terminalRounds d T) t) := by
  have hFn : (fun ω : CoinSpace T ↦ (terminalCount d T (finalStart d (coinPath ω) T):ℝ))=
      fun ω ↦ ((∑ t : Fin T, if Terminal d T t.val ∧ t.val<finalStart d (coinPath ω) T then 1 else 0 : ℕ):ℝ) := by
    funext ω
    exact congrArg (fun n : ℕ ↦ (n:ℝ)) (missed_count_eq d ω)
  rw [hFn,Tournament.Probability.integral_nat_count (coinLaw T p) (Finset.univ : Finset (Fin T))
    (fun (ω : CoinSpace T) (t : Fin T) ↦ Terminal d T t.val ∧ t.val<finalStart d (coinPath ω) T)]
  change _=∑ t∈Finset.univ.filter (fun t : Fin T ↦ Terminal d T t.val),
    (1-(p:ℝ))^(Tournament.Probability.inclusiveRank (terminalRounds d T) t)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hTerm : Terminal d T t.val
  · simp only [hTerm,true_and,ite_true]
    exact before_boundary_probability d p t
  · simp [hTerm]

theorem expected_missed_count_le (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) (hp : 0<(p:ℝ)) :
    (∫ ω, (terminalCount d T (finalStart d (coinPath ω) T):ℝ) ∂coinLaw T p)≤(1-(p:ℝ))/(p:ℝ) := by
  rw [expected_missed_count_eq]
  have h := Tournament.Probability.ordered_geometric_tail (terminalRounds d T) (1-(p:ℝ))
    (by linarith [p.2.2]) (by linarith)
  simpa only [show (1:ℝ)-(1-(p:ℝ))=(p:ℝ) by ring] using h

theorem expected_missed_advantage (d : ℕ → ℝ) (T : ℕ) (p : unitInterval) (hp : 0<(p:ℝ))
    (hd : ∀ t<T, -1≤d t ∧ d t≤1) :
    (∫ ω, -restingGain d (coinPath ω) T ∂coinLaw T p)≤
      1/(p:ℝ)+(∫ ω, (probeCount d (coinPath ω) T:ℝ) ∂coinLaw T p) := by
  have h := integral_mono (μ := coinLaw T p) Integrable.of_finite Integrable.of_finite
    (fun ω ↦ missed_advantage_pathwise d (coinPath ω) T hd)
  change (∫ ω, -restingGain d (coinPath ω) T ∂coinLaw T p)≤
    ∫ ω, (terminalCount d T (finalStart d (coinPath ω) T):ℝ)+(probeCount d (coinPath ω) T:ℝ) ∂coinLaw T p at h
  rw [integral_add Integrable.of_finite Integrable.of_finite] at h
  have hMiss := expected_missed_count_le d T p hp
  have hRatio : (1-(p:ℝ))/(p:ℝ)≤1/(p:ℝ) :=
    div_le_div_of_nonneg_right (by linarith [p.2.1]) hp.le
  linarith

end
end Tournament.Upper.GeometricProbing
