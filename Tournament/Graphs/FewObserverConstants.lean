module

public import Tournament.Graphs.FewObserverMoments

@[expose] public section

namespace Tournament.ObserverSampling

open scoped Classical
noncomputable section

def threshold (K : ℕ) : ℕ := ⌈Real.log (K:ℝ)⌉₊+1

def samplingRate (f n : ℝ) : ℝ := 1/(4*f*n)

theorem threshold_observer_bound (K : ℕ) (hK : 2≤K) :
    ((threshold K-1:ℕ):ℝ)≤1+Real.log (K:ℝ) := by
  have hlog := Upper.Tuning.log_card_lower hK
  have h := Nat.ceil_lt_add_one (show 0≤Real.log (K:ℝ) by linarith)
  simp only [threshold,Nat.add_sub_cancel]
  linarith

theorem threshold_tail_bound (K : ℕ) (hK : 2≤K) :
    (K:ℝ)*(4/3:ℝ)*(1/4:ℝ)^(threshold K)≤1/3 := by
  have hK0 : 0<(K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have hLog := Upper.Tuning.log_card_lower hK
  have hLog4 : 1≤Real.log (4:ℝ) := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
    linarith [Upper.Tuning.log_two_lower]
  have hCeil := Nat.le_ceil (Real.log (K:ℝ))
  have hPower : (K:ℝ)≤(4:ℝ)^⌈Real.log (K:ℝ)⌉₊ := by
    calc
      _ = Real.exp (Real.log (K:ℝ)) := (Real.exp_log hK0).symm
      _ ≤ Real.exp ((⌈Real.log (K:ℝ)⌉₊:ℝ)*Real.log (4:ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
  have hDiv : (K:ℝ)/(4:ℝ)^⌈Real.log (K:ℝ)⌉₊≤1 := (div_le_one (by positivity)).mpr hPower
  have hFactor : (K:ℝ)*(4/3:ℝ)*(1/4:ℝ)^(threshold K)=
      (1/3:ℝ)*((K:ℝ)/(4:ℝ)^⌈Real.log (K:ℝ)⌉₊) := by
    unfold threshold
    rw [one_div_pow,pow_succ]
    ring
  rw [hFactor]
  nlinarith

theorem samplingRate_bounds (f n : ℝ) (hfn : 1≤f*n) :
    0<samplingRate f n ∧ samplingRate f n≤1/4 := by
  have hDen : 0<4*f*n := by nlinarith
  constructor
  · exact one_div_pos.mpr hDen
  · apply (div_le_iff₀ hDen).mpr
    nlinarith

theorem samplingRate_pair_cost (f n : ℝ) (hf : 0<f) (hn : 0<n) :
    (samplingRate f n)^2*n*f*n=samplingRate f n*n/4 := by
  unfold samplingRate
  field_simp

theorem samplingRate_mean_size (K γ : ℕ) (hK : 2≤K) (hγ : 2≤γ) (n : ℝ) (hn : 0<n) :
    samplingRate (ObserverThinning.fraction K γ) n*n=(γ:ℝ)/(8*Real.log (K:ℝ)) := by
  have hLog : 0<Real.log (K:ℝ) := by linarith [Upper.Tuning.log_card_lower hK]
  have hγ0 : (γ:ℝ)≠0 := by exact_mod_cast (by omega : γ≠0)
  unfold samplingRate ObserverThinning.fraction
  field_simp
  norm_num

theorem final_size_arithmetic (K γ : ℕ) (hK : 2≤K) (hLarge : 32*Real.log (K:ℝ)≤(γ:ℝ))
    (n : ℝ) (hn : 0<n) :
    (γ:ℝ)/(16*Real.log (K:ℝ))≤samplingRate (ObserverThinning.fraction K γ) n*n-1/3-
      (samplingRate (ObserverThinning.fraction K γ) n)^2*n*(ObserverThinning.fraction K γ)*n := by
  rcases ObserverThinning.fraction_bounds K γ hK hLarge with ⟨hγ,hf,_⟩
  rw [samplingRate_pair_cost _ _ hf hn,samplingRate_mean_size K γ hK hγ n hn]
  have hLog : 0<Real.log (K:ℝ) := by linarith [Upper.Tuning.log_card_lower hK]
  have hRatio : 1≤(γ:ℝ)/(32*Real.log (K:ℝ)) := (one_le_div (by positivity)).mpr hLarge
  have hIdentity : (γ:ℝ)/(8*Real.log (K:ℝ))-(γ:ℝ)/(8*Real.log (K:ℝ))/4-
      (γ:ℝ)/(16*Real.log (K:ℝ))=(γ:ℝ)/(32*Real.log (K:ℝ)) := by ring
  linarith

end
end Tournament.ObserverSampling
