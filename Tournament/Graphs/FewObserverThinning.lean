module

public import Tournament.Graphs.ObserverThinning
public import Tournament.Upper.Tuning

@[expose] public section

namespace Tournament.ObserverThinning

open scoped Classical
noncomputable section

def fraction (K γ : ℕ) : ℝ := 2*Real.log (K:ℝ)/(γ:ℝ)

theorem fraction_bounds (K γ : ℕ) (hK : 2≤K) (hLarge : 32*Real.log (K:ℝ)≤(γ:ℝ)) :
    2≤γ ∧ 0<fraction K γ ∧ fraction K γ≤1/16 := by
  have hlog := Upper.Tuning.log_card_lower hK
  have hγr : (2:ℝ)≤(γ:ℝ) := by linarith
  have hγ : 2≤γ := by exact_mod_cast hγr
  have hγpos : 0<(γ:ℝ) := by linarith
  refine ⟨hγ,div_pos (by linarith) hγpos,?_⟩
  apply (div_le_iff₀ hγpos).mpr
  linarith

theorem fraction_decay (K γ : ℕ) (hK : 2≤K) (hLarge : 32*Real.log (K:ℝ)≤(γ:ℝ)) :
    (K:ℝ)*(1-fraction K γ)^(γ-1)≤1 := by
  rcases fraction_bounds K γ hK hLarge with ⟨hγ,hf,hf16⟩
  have hK0 : 0<(K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have hγ0 : (γ:ℝ)≠0 := by exact_mod_cast (by omega : γ≠0)
  have hFrac : fraction K γ*(γ:ℝ)/2=Real.log (K:ℝ) := by
    unfold fraction
    field_simp
  have hExp : 1-fraction K γ≤Real.exp (-fraction K γ) := by
    have h := Real.add_one_le_exp (-fraction K γ)
    linarith
  have hPow := pow_le_pow_left₀ (show 0≤1-fraction K γ by linarith) hExp (γ-1)
  rw [← Real.exp_nat_mul] at hPow
  have hr : (γ:ℝ)/2≤((γ-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤γ),Nat.cast_one]
    have hγr : (2:ℝ)≤(γ:ℝ) := by exact_mod_cast hγ
    linarith
  have hE : Real.exp (((γ-1:ℕ):ℝ)*(-fraction K γ))≤Real.exp (-Real.log (K:ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [← hFrac]
    nlinarith
  calc
    _ ≤ (K:ℝ)*Real.exp (-Real.log (K:ℝ)) := mul_le_mul_of_nonneg_left (hPow.trans hE) hK0.le
    _ = _ := by rw [Real.exp_neg,Real.exp_log hK0]; field_simp

variable {ι : Type*} [Fintype ι]

theorem exists_source_thin_set (E : ι → ι → Prop) (hE : Observable E) (hK : 2≤Fintype.card ι)
    (hLarge : 32*Real.log (Fintype.card ι:ℝ)≤(dominationNumber E hE:ℝ)) :
    ∃ W : Finset ι, W.Nonempty ∧
      (∀ a, ((observedMembers E W a).card:ℝ)≤fraction (Fintype.card ι) (dominationNumber E hE)*(W.card:ℝ)) ∧
      1≤fraction (Fintype.card ι) (dominationNumber E hE)*(W.card:ℝ) := by
  rcases fraction_bounds (Fintype.card ι) (dominationNumber E hE) hK hLarge with ⟨hγ,_,hf⟩
  exact exists_thin_remainder E hE (fraction (Fintype.card ι) (dominationNumber E hE)) (by linarith)
    (dominationNumber E hE-1) (by omega) (by omega)
    (fraction_decay (Fintype.card ι) (dominationNumber E hE) hK hLarge)

end
end Tournament.ObserverThinning
