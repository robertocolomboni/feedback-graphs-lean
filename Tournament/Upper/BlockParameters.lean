module

public import Tournament.Upper.OptimalPreparation
public import Tournament.Upper.ScoreTail

@[expose] public section

namespace Tournament.Upper.BlockParameters

open scoped BigOperators Classical

noncomputable section

def logScale (K T : ℕ) : ℝ := Real.log (Real.exp 1*(K:ℝ)*(T:ℝ))
def failure (K T : ℕ) : ℝ := 1/(((K:ℝ)*(T:ℝ))^20)
def threshold (K T : ℕ) : ℝ := 100*Real.log (2/failure K T)
def learningRate (K T m : ℕ) : ℝ := DyadicRate.base m/((2:ℝ)^25*threshold K T*(m:ℝ)*logScale K T)
def paymentCoefficient (K T m : ℕ) : ℝ := DyadicRate.base m/((2:ℝ)^24*threshold K T*(m:ℝ)*logScale K T)
def horizon (m : ℕ) : ℕ := 2^(m-3)
def meanRate (m : ℕ) : ℝ := DyadicRate.base m*(1+(m:ℝ)/2)

theorem product_ge_four {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : (4:ℝ)≤(K:ℝ)*(T:ℝ) := by
  have hk : (2:ℝ)≤(K:ℝ) := by exact_mod_cast hK
  have ht : (2:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  nlinarith

theorem failure_pos {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : 0<failure K T := by
  have hprod : 0<(K:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (product_ge_four hK hT)
  unfold failure
  positivity

theorem failure_le_one {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : failure K T≤1 := by
  have hp : (1:ℝ)≤(K:ℝ)*(T:ℝ) := le_trans (by norm_num) (product_ge_four hK hT)
  have hpow : (1:ℝ)≤((K:ℝ)*(T:ℝ))^20 := one_le_pow₀ hp
  unfold failure
  exact (div_le_one (by linarith : (0:ℝ)<((K:ℝ)*(T:ℝ))^20)).mpr hpow

theorem logScale_ge_one {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : 1≤logScale K T := by
  have hp : (1:ℝ)≤(K:ℝ)*(T:ℝ) := le_trans (by norm_num) (product_ge_four hK hT)
  have hp0 : (K:ℝ)*(T:ℝ)≠0 := by linarith
  have hl := Real.log_nonneg hp
  unfold logScale
  rw [mul_assoc,Real.log_mul (ne_of_gt (Real.exp_pos 1)) hp0,Real.log_exp]
  linarith

theorem threshold_ge_one {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : 1≤threshold K T :=
  TailConstants.threshold_ge_one (failure_pos hK hT) (failure_le_one hK hT) (le_refl _)

theorem base_le_one_thirtytwo {m : ℕ} (hm : 5≤m) : DyadicRate.base m≤1/32 := by
  have hp : (32:ℝ)≤2^m := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hm
    norm_num at h
    exact h
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<32) hp
  simpa only [DyadicRate.base_eq_inv_pow,one_div] using hi

theorem learningRate_pos {K T m : ℕ} (hK : 2≤K) (hT : 2≤T) (hm : 5≤m) : 0<learningRate K T m := by
  have hM : 0<threshold K T := lt_of_lt_of_le (by norm_num) (threshold_ge_one hK hT)
  have hΛ : 0<logScale K T := lt_of_lt_of_le (by norm_num) (logScale_ge_one hK hT)
  have hm0 : (0:ℝ)<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  unfold learningRate
  exact div_pos (DyadicRate.base_pos m) (by positivity)

theorem horizon_mul_base {m : ℕ} (hm : 3≤m) : (horizon m:ℝ)*DyadicRate.base m=1/8 := by
  have hpow : (2:ℝ)^m=8*(horizon m:ℝ) := by
    unfold horizon
    rw [Nat.cast_pow,Nat.cast_ofNat,← Nat.sub_add_cancel hm,pow_add]
    norm_num
    ring
  have hid := DyadicRate.base_mul_pow m
  rw [hpow] at hid
  nlinarith

theorem short_block {m h : ℕ} (hm : 3≤m) (hh : h≤horizon m) : (h:ℝ)*DyadicRate.base m≤1/8 := by
  have hcast : (h:ℝ)≤(horizon m:ℝ) := by exact_mod_cast hh
  exact le_trans (mul_le_mul_of_nonneg_right hcast (DyadicRate.base_pos m).le) (le_of_eq (horizon_mul_base hm))

theorem horizon_eq {m : ℕ} (hm : 3≤m) : (horizon m:ℝ)=1/(8*DyadicRate.base m) := by
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (DyadicRate.base_pos m)))).mpr
  have h := horizon_mul_base hm
  nlinarith

theorem meanRate_nonneg (m : ℕ) : 0≤meanRate m :=
  mul_nonneg (DyadicRate.base_pos m).le (by positivity)

theorem base_le_meanRate (m : ℕ) : DyadicRate.base m≤meanRate m := by
  unfold meanRate
  have hmul := mul_nonneg (DyadicRate.base_pos m).le (show (0:ℝ)≤(m:ℝ)/2 by positivity)
  nlinarith

theorem twice_learningRate (K T m : ℕ) : 2*learningRate K T m=paymentCoefficient K T m := by
  unfold learningRate paymentCoefficient
  norm_num
  ring

variable {ι : Type*} [Fintype ι]

theorem minimumWeight_floor (w : ProbabilityVector ι) (T : ℕ)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    1/((Fintype.card ι:ℝ)*(T:ℝ))≤w.minimumWeight := by
  have : Nonempty ι := w.nonempty
  apply Finset.le_inf'
  intro i _
  exact hwfloor i

theorem anchorLog_le_logScale (w : ProbabilityVector ι) (hw : ∀ i, 0<w i)
    {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    w.anchorLog≤logScale (Fintype.card ι) T := by
  have hmin := w.minimumWeight_pos hw
  have hp : 0<(Fintype.card ι:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (product_ge_four hK hT)
  have hmul := (div_le_iff₀ hp).mp (minimumWeight_floor w T hwfloor)
  unfold ProbabilityVector.anchorLog logScale
  apply Real.log_le_log (div_pos (Real.exp_pos 1) hmin)
  apply (div_le_iff₀ hmin).mpr
  calc
    Real.exp 1 = Real.exp 1*1 := by ring
    _ ≤ Real.exp 1*(w.minimumWeight*((Fintype.card ι:ℝ)*(T:ℝ))) :=
      mul_le_mul_of_nonneg_left hmul (Real.exp_pos 1).le
    _ = _ := by ring

theorem estimatorConstant_le (w : ProbabilityVector ι) (hw : ∀ i, 0<w i)
    {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    128*w.anchorLog≤(2:ℝ)^8*logScale (Fintype.card ι) T := by
  have hl := anchorLog_le_logScale w hw hK hT hwfloor
  have hΛ := logScale_ge_one hK hT
  norm_num
  linarith

theorem truncation_threshold_fits {K T m : ℕ} (hK : 2≤K) (hT : 2≤T) (hm : 5≤m)
    (L₀ : ℝ) (hL₀ : L₀≤(2:ℝ)^8*logScale K T) :
    learningRate K T m*(2*threshold K T*L₀/DyadicRate.base m)≤1 := by
  have hM : 0<threshold K T := lt_of_lt_of_le (by norm_num) (threshold_ge_one hK hT)
  have hΛ : 0<logScale K T := lt_of_lt_of_le (by norm_num) (logScale_ge_one hK hT)
  have hm1 : (1:ℝ)≤(m:ℝ) := by exact_mod_cast (show 1≤m by omega)
  have hm0 : (0:ℝ)<(m:ℝ) := by linarith
  have hκ := DyadicRate.base_pos m
  calc
    _ = L₀/((2:ℝ)^24*(m:ℝ)*logScale K T) := by
      unfold learningRate
      field_simp
    _ ≤ 1 := by
      apply (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^24*(m:ℝ)*logScale K T)).mpr
      have hmΛ := mul_le_mul_of_nonneg_right hm1 hΛ.le
      norm_num at hL₀ ⊢
      nlinarith

end
end Tournament.Upper.BlockParameters
