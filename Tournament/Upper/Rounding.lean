module

public import Tournament.Upper.BlockParameters
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Cast.Defs

@[expose] public section

namespace Tournament.Upper.Rounding

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def scale (T : ℕ) : ℕ := 4*Fintype.card ι*T
def numerator (w : ProbabilityVector ι) (T : ℕ) (i : ι) : ℕ := ⌈(scale (ι := ι) T:ℝ)*w i⌉₊
def denominator (w : ProbabilityVector ι) (T : ℕ) : ℕ := ∑ i, numerator w T i

theorem numerator_lower (w : ProbabilityVector ι) (T : ℕ) (i : ι) :
    (scale (ι := ι) T:ℝ)*w i≤(numerator w T i:ℝ) := Nat.le_ceil _

theorem numerator_upper (w : ProbabilityVector ι) (T : ℕ) (i : ι) :
    (numerator w T i:ℝ)≤(scale (ι := ι) T:ℝ)*w i+1 :=
  (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (w.nonneg i))).le

theorem numerator_le_scale (w : ProbabilityVector ι) (T : ℕ) (i : ι) : numerator w T i≤scale (ι := ι) T := by
  apply Nat.ceil_le.mpr
  have h := mul_le_mul_of_nonneg_left (w.weight_le_one i) (show (0:ℝ)≤(scale (ι := ι) T:ℝ) by positivity)
  simpa only [mul_one] using h

theorem denominator_lower (w : ProbabilityVector ι) (T : ℕ) : (scale (ι := ι) T:ℝ)≤(denominator w T:ℝ) := by
  calc
    _ = ∑ i, (scale (ι := ι) T:ℝ)*w i := by rw [← Finset.mul_sum,w.sum_eq_one,mul_one]
    _ ≤ ∑ i, (numerator w T i:ℝ) := Finset.sum_le_sum (fun i _ ↦ numerator_lower w T i)
    _ = _ := by simp [denominator]

theorem denominator_upper (w : ProbabilityVector ι) (T : ℕ) :
    (denominator w T:ℝ)≤(scale (ι := ι) T:ℝ)+(Fintype.card ι:ℝ) := by
  calc
    _ = ∑ i, (numerator w T i:ℝ) := by simp [denominator]
    _ ≤ ∑ i, ((scale (ι := ι) T:ℝ)*w i+1) := Finset.sum_le_sum (fun i _ ↦ numerator_upper w T i)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,w.sum_eq_one]; simp

theorem scale_pos (w : ProbabilityVector ι) {T : ℕ} (hT : 0<T) : (0:ℝ)<(scale (ι := ι) T:ℝ) := by
  have : Nonempty ι := w.nonempty
  have hK : (0:ℝ)<(Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hT' : (0:ℝ)<(T:ℝ) := by exact_mod_cast hT
  unfold scale
  push_cast
  positivity

theorem denominator_pos (w : ProbabilityVector ι) {T : ℕ} (hT : 0<T) : (0:ℝ)<(denominator w T:ℝ) :=
  lt_of_lt_of_le (scale_pos w hT) (denominator_lower w T)

def anchor (w : ProbabilityVector ι) (T : ℕ) (hT : 0<T) : ProbabilityVector ι where
  weight i := (numerator w T i:ℝ)/(denominator w T:ℝ)
  nonneg i := div_nonneg (Nat.cast_nonneg _) (denominator_pos w hT).le
  sum_eq_one := by
    rw [← Finset.sum_div]
    have hsum : (∑ i, (numerator w T i:ℝ))=(denominator w T:ℝ) := by simp [denominator]
    rw [hsum]
    exact div_self (ne_of_gt (denominator_pos w hT))

theorem denominator_le_nine_eighths (w : ProbabilityVector ι) {T : ℕ} (hT : 2≤T) :
    (denominator w T:ℝ)≤(9/8)*(scale (ι := ι) T:ℝ) := by
  have hden := denominator_upper w T
  have ht : (2:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  have hk : (0:ℝ)≤(Fintype.card ι:ℝ) := by positivity
  have hKT := mul_le_mul_of_nonneg_left ht hk
  unfold scale at *
  push_cast at *
  nlinarith

theorem scaled_weight_ge_four (w : ProbabilityVector ι) {T : ℕ}
    (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    (4:ℝ)≤(scale (ι := ι) T:ℝ)*w i := by
  have hp : 0<(Fintype.card ι:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (BlockParameters.product_ge_four hK hT)
  have hmul := (div_le_iff₀ hp).mp (hwfloor i)
  unfold scale
  push_cast
  nlinarith

theorem input_pos_of_floor (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) : 0<w i := by
  have hp : 0<(Fintype.card ι:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (BlockParameters.product_ge_four hK hT)
  exact lt_of_lt_of_le (one_div_pos.mpr hp) (hwfloor i)

theorem numerator_le_five_fourths (w : ProbabilityVector ι) {T : ℕ}
    (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    (numerator w T i:ℝ)≤(5/4)*(scale (ι := ι) T:ℝ)*w i := by
  have hl := scaled_weight_ge_four w hK hT hwfloor i
  have hu := numerator_upper w T i
  nlinarith

theorem anchor_bounds (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    (8/9)*w i≤anchor w T (by omega) i ∧ anchor w T (by omega) i≤(5/4)*w i := by
  have hd := denominator_pos w (show 0<T by omega)
  constructor
  · apply (le_div_iff₀ hd).mpr
    have hden := mul_le_mul_of_nonneg_right (denominator_le_nine_eighths w hT)
      (show 0≤(8/9)*w i from mul_nonneg (by norm_num) (w.nonneg i))
    have hnum := numerator_lower w T i
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hden := mul_le_mul_of_nonneg_right (denominator_lower w T)
      (show 0≤(5/4)*w i from mul_nonneg (by norm_num) (w.nonneg i))
    have hnum := numerator_le_five_fourths w hK hT hwfloor i
    nlinarith

theorem anchor_weight_floor (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    8/(9*(Fintype.card ι:ℝ)*(T:ℝ))≤anchor w T (by omega) i := by
  calc
    _ = (8/9)*(1/((Fintype.card ι:ℝ)*(T:ℝ))) := by ring
    _ ≤ (8/9)*w i := mul_le_mul_of_nonneg_left (hwfloor i) (by norm_num)
    _ ≤ _ := (anchor_bounds w hK hT hwfloor i).1

theorem anchor_pos (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    0<anchor w T (by omega) i := by
  have hp : 0<(Fintype.card ι:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (BlockParameters.product_ge_four hK hT)
  exact lt_of_lt_of_le (by positivity) (anchor_weight_floor w hK hT hwfloor i)

theorem anchor_minimum_floor (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    8/(9*(Fintype.card ι:ℝ)*(T:ℝ))≤(anchor w T (by omega)).minimumWeight := by
  have : Nonempty ι := w.nonempty
  apply Finset.le_inf'
  intro i _
  exact anchor_weight_floor w hK hT hwfloor i

theorem anchorLog_le_four_thirds (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    (anchor w T (by omega)).anchorLog≤(4/3)*BlockParameters.logScale (Fintype.card ι) T := by
  let v := anchor w T (show 0<T by omega)
  have hv : 0<v.minimumWeight := v.minimumWeight_pos (anchor_pos w hK hT hwfloor)
  have hp : 0<(Fintype.card ι:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (BlockParameters.product_ge_four hK hT)
  have hfloor := anchor_minimum_floor w hK hT hwfloor
  have hinv : 1/v.minimumWeight≤(9/8)*((Fintype.card ι:ℝ)*(T:ℝ)) := by
    have h := one_div_le_one_div_of_le (show 0<8/(9*(Fintype.card ι:ℝ)*(T:ℝ)) by positivity) hfloor
    calc
      _ ≤ 1/(8/(9*(Fintype.card ι:ℝ)*(T:ℝ))) := h
      _ = _ := by field_simp
  have hlogratio : Real.log (9/8:ℝ)≤1/8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9/8)
    norm_num at h
    exact h
  have hΛ := BlockParameters.logScale_ge_one hK hT
  calc
    _ ≤ Real.log ((Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ))*(9/8)) := by
      apply Real.log_le_log (div_pos (Real.exp_pos 1) hv)
      have hm := mul_le_mul_of_nonneg_left hinv (Real.exp_pos 1).le
      change Real.exp 1/v.minimumWeight≤(Real.exp 1*(Fintype.card ι:ℝ)*(T:ℝ))*(9/8)
      calc
        _ = Real.exp 1*(1/v.minimumWeight) := by ring
        _ ≤ Real.exp 1*((9/8)*((Fintype.card ι:ℝ)*(T:ℝ))) := hm
        _ = _ := by ring
    _ = BlockParameters.logScale (Fintype.card ι) T+Real.log (9/8) := by
      rw [Real.log_mul (by positivity) (by norm_num)]
      rfl
    _ ≤ _ := by linarith

theorem numerator_denominator_bounds (w : ProbabilityVector ι) {T : ℕ} (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (i : ι) :
    1≤numerator w T i ∧ numerator w T i≤4*Fintype.card ι*T ∧ denominator w T≤5*Fintype.card ι*T := by
  have hreal : (1:ℝ)≤(numerator w T i:ℝ) := by
    have hn := numerator_lower w T i
    have hw := scaled_weight_ge_four w hK hT hwfloor i
    linarith
  have hd := denominator_le_nine_eighths w hT
  have hdreal : (denominator w T:ℝ)≤5*(Fintype.card ι:ℝ)*(T:ℝ) := by
    unfold scale at hd
    push_cast at hd
    have hp := BlockParameters.product_ge_four hK hT
    nlinarith
  exact ⟨by exact_mod_cast hreal,numerator_le_scale w T i,by exact_mod_cast hdreal⟩

theorem anchor_is_rational (w : ProbabilityVector ι) (T : ℕ) (hT : 0<T) (i : ι) :
    ∃ q : ℚ, (q:ℝ)=anchor w T hT i := by
  refine ⟨(numerator w T i:ℚ)/(denominator w T:ℚ),?_⟩
  push_cast
  rfl

end
end Tournament.Upper.Rounding
