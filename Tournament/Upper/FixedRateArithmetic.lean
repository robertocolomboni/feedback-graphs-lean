module

public import Tournament.Upper.BlockParameters
public import Tournament.Model.UniformSchedule
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace Tournament.Upper.BlockParameters

open scoped BigOperators Classical
open Model

noncomputable section

theorem logScale_le_product {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    logScale K T≤(K:ℝ)*(T:ℝ) := by
  have hp : (0:ℝ)<(K:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (product_ge_four hK hT)
  unfold logScale
  rw [mul_assoc,Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hp),Real.log_exp]
  linarith [Real.log_le_sub_one_of_pos hp]

theorem time_le_product {K T : ℕ} (hK : 2≤K) : (T:ℝ)≤(K:ℝ)*(T:ℝ) := by
  have hk : (1:ℝ)≤(K:ℝ) := by exact_mod_cast (show 1≤K by omega)
  nlinarith [show (0:ℝ)≤(T:ℝ) by positivity]

theorem rare_event_sum_lt_one {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    failure K T*(T:ℝ)^3+128*failure K T*logScale K T*(T:ℝ)^2<1 := by
  let p : ℝ := (K:ℝ)*(T:ℝ)
  have hp : 4≤p := product_ge_four hK hT
  have hp0 : 0<p := by linarith
  have ht : (T:ℝ)≤p := time_le_product hK
  have hΛ : logScale K T≤p := logScale_le_product hK hT
  have hδ : 0≤failure K T := (failure_pos hK hT).le
  have heq : failure K T*p^3=1/p^17 := by
    change (1/p^20)*p^3=1/p^17
    field_simp
  have hfirst : failure K T*(T:ℝ)^3≤failure K T*p^3 := by gcongr
  have hsecond : 128*failure K T*logScale K T*(T:ℝ)^2≤128*failure K T*p^3 := by
    calc
      _ ≤ 128*failure K T*p*p^2 := by gcongr
      _ = _ := by ring
  have hpow : (4:ℝ)^17≤p^17 := pow_le_pow_left₀ (by norm_num) hp 17
  have hsmall : 129/p^17<1 := by
    apply (div_lt_one (pow_pos hp0 17)).mpr
    norm_num at hpow
    linarith
  calc
    _ ≤ 129*(failure K T*p^3) := by linarith
    _ = 129/p^17 := by rw [heq]; ring
    _ < 1 := hsmall

theorem uniform_count_bound {m : ℕ} (hm : 5≤m) (T : ℕ) :
    (UniformSchedule.count T (horizon m):ℝ)≤8*DyadicRate.base m*(T:ℝ)+1 := by
  have hHκ : (horizon m:ℝ)*(8*DyadicRate.base m)=1 := by
    have h := horizon_mul_base (show 3≤m by omega)
    nlinarith
  have hc : (UniformSchedule.count T (horizon m):ℝ)*(horizon m:ℝ)≤(T:ℝ)+(horizon m:ℝ) := by
    exact_mod_cast UniformSchedule.count_mul_le T (horizon m)
  calc
    _ = (UniformSchedule.count T (horizon m):ℝ)*((horizon m:ℝ)*(8*DyadicRate.base m)) := by rw [hHκ]; ring
    _ = ((UniformSchedule.count T (horizon m):ℝ)*(horizon m:ℝ))*(8*DyadicRate.base m) := by ring
    _ ≤ ((T:ℝ)+(horizon m:ℝ))*(8*DyadicRate.base m) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num) (DyadicRate.base_pos m).le)
    _ = 8*DyadicRate.base m*(T:ℝ)+(horizon m:ℝ)*(8*DyadicRate.base m) := by ring
    _ = _ := by rw [hHκ]

theorem sum_cubes_le (h : ℕ → ℕ) (B T : ℕ) (htotal : prefixHorizon h B=T) :
    (∑ b ∈ Finset.range B, (h b:ℝ)^3)≤(T:ℝ)^3 := by
  have hsum : (∑ b ∈ Finset.range B, (h b:ℝ))=(T:ℝ) := by
    exact_mod_cast htotal
  calc
    _ ≤ ∑ b ∈ Finset.range B, (h b:ℝ)*(T:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hbT : h b≤T := by
        rw [← htotal]
        exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hb
      have hbTr : (h b:ℝ)≤(T:ℝ) := by exact_mod_cast hbT
      calc
        (h b:ℝ)^3=(h b:ℝ)*(h b:ℝ)^2 := by ring
        _ ≤ _ := by gcongr
    _ = (T:ℝ)^3 := by rw [← Finset.sum_mul,hsum]; ring

theorem total_rare_charge_lt_one {K T m : ℕ} (hK : 2≤K) (hT : 2≤T)
    (hκ : 1/(T:ℝ)≤DyadicRate.base m) (h : ℕ → ℕ) (B : ℕ)
    (htotal : prefixHorizon h B=T) :
    (∑ b ∈ Finset.range B, (failure K T*(h b:ℝ)^3+
      (2:ℝ)^7*failure K T*(h b:ℝ)*logScale K T/DyadicRate.base m))<1 := by
  have hδ : 0≤failure K T := (failure_pos hK hT).le
  have hΛ : 0≤logScale K T := le_trans (by norm_num) (logScale_ge_one hK hT)
  have hT0 : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hinv : 1/DyadicRate.base m≤(T:ℝ) := by
    apply (div_le_iff₀ (DyadicRate.base_pos m)).mpr
    have hh := (div_le_iff₀ hT0).mp hκ
    nlinarith
  have hsum : (∑ b ∈ Finset.range B, (h b:ℝ))=(T:ℝ) := by exact_mod_cast htotal
  have heq : (∑ b ∈ Finset.range B, (failure K T*(h b:ℝ)^3+
      (2:ℝ)^7*failure K T*(h b:ℝ)*logScale K T/DyadicRate.base m))=
      failure K T*(∑ b ∈ Finset.range B, (h b:ℝ)^3)+
        (128*failure K T*logScale K T/DyadicRate.base m)*(T:ℝ) := by
    rw [← hsum]
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    norm_num
    ring
  rw [heq]
  calc
    _ ≤ failure K T*(T:ℝ)^3+128*failure K T*logScale K T*(T:ℝ)^2 := by
      have hc := mul_le_mul_of_nonneg_left (sum_cubes_le h B T htotal) hδ
      have hb := mul_le_mul_of_nonneg_left hinv (show 0≤128*failure K T*logScale K T*(T:ℝ) by positivity)
      simp only [div_eq_mul_inv,one_mul] at hb ⊢
      nlinarith only [hc,hb]
    _ < 1 := rare_event_sum_lt_one hK hT

end
end Tournament.Upper.BlockParameters
