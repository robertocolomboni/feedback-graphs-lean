module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Probability

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem binomial_probability_le (n b : ℕ) (q : ℝ) (hq : 0≤q) (hq1 : q≤1) :
    (n.choose b:ℝ)*q^b*(1-q)^(n-b)≤((n:ℝ)*q)^b/(b.factorial:ℝ) := by
  have hp : (1-q)^(n-b)≤1 := pow_le_one₀ (by linarith) (by linarith)
  calc
    _ ≤ (n.choose b:ℝ)*q^b := mul_le_of_le_one_right (by positivity) hp
    _ ≤ ((n:ℝ)^b/(b.factorial:ℝ))*q^b :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div b n) (pow_nonneg hq _)
    _ = _ := by rw [mul_pow]; ring

theorem weighted_binomial_probability_le (n b : ℕ) (q : ℝ) (hq : 0≤q) (hq1 : q≤1)
    (hnq : (n:ℝ)*q≤1/4) :
    (b:ℝ)*((n.choose b:ℝ)*q^b*(1-q)^(n-b))≤(1/4:ℝ)^b := by
  have hFac : (b:ℝ)≤(b.factorial:ℝ) := by exact_mod_cast Nat.self_le_factorial b
  have hFac0 : 0<(b.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos b
  have hPower : ((n:ℝ)*q)^b≤(1/4:ℝ)^b := pow_le_pow_left₀ (by positivity) hnq b
  have hBase := (binomial_probability_le n b q hq hq1).trans
    (div_le_div_of_nonneg_right hPower hFac0.le)
  calc
    _ ≤ (b:ℝ)*((1/4:ℝ)^b/(b.factorial:ℝ)) := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hFac0).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hFac (show 0≤(1/4:ℝ)^b by positivity)

theorem geometric_tail_sum (k N : ℕ) :
    (∑ b∈Finset.range (N+1), if k≤b then (1/4:ℝ)^b else 0)≤(4/3:ℝ)*(1/4:ℝ)^k := by
  rw [← Finset.sum_filter]
  have hFilter : (Finset.range (N+1)).filter (fun b ↦ k≤b)=Finset.Ico k (N+1) := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico,and_comm]
  rw [hFilter]
  have h := geom_sum_Ico_le_of_lt_one (show (0:ℝ)≤1/4 by norm_num) (show (1/4:ℝ)<1 by norm_num)
    (m := k) (n := N+1)
  norm_num at h
  nlinarith [h]

theorem integral_bounded_nat {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ) (N : ℕ) (hX : ∀ ω, X ω≤N) (F : ℕ → ℝ) :
    (∫ ω, F (X ω) ∂μ)=∑ b∈Finset.range (N+1), F b*μ.real {ω | X ω=b} := by
  have hEq : (fun ω ↦ F (X ω))=(fun ω ↦ ∑ b∈Finset.range (N+1), if X ω=b then F b else 0) := by
    funext ω
    simp [Nat.lt_succ_of_le (hX ω)]
  rw [hEq,integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro b _
  have hi : (fun ω ↦ if X ω=b then F b else 0)=({ω | X ω=b}).indicator (fun _ ↦ F b) := by
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  rw [hi,integral_indicator_const _ (MeasurableSet.of_discrete)]
  simp only [smul_eq_mul,mul_comm]

theorem integral_card_filter {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (P : Ω → ι → Prop) :
    (∫ ω, ((s.filter (P ω)).card:ℝ) ∂μ)=∑ i∈s, μ.real {ω | P ω i} := by
  have hEq : (fun ω ↦ ((s.filter (P ω)).card:ℝ))=
      fun ω ↦ ∑ i∈s, ({ω | P ω i}).indicator (1 : Ω → ℝ) ω := by
    funext ω
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      Set.indicator_apply,Set.mem_ofPred_eq,Pi.one_apply]
  rw [hEq,integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  exact Finset.sum_congr rfl (fun i _ ↦ integral_indicator_one (MeasurableSet.of_discrete))

theorem integral_binomial_tail {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ) (N k : ℕ) (hX : ∀ ω, X ω≤N)
    (q : ℝ) (hq : 0≤q) (hq1 : q≤1) (hNq : (N:ℝ)*q≤1/4)
    (hLaw : ∀ b, μ.real {ω | X ω=b}=(N.choose b:ℝ)*q^b*(1-q)^(N-b)) :
    (∫ ω, if k≤X ω then (X ω:ℝ) else 0 ∂μ)≤(4/3:ℝ)*(1/4:ℝ)^k := by
  rw [integral_bounded_nat μ X N hX (fun b ↦ if k≤b then (b:ℝ) else 0)]
  calc
    _ ≤ ∑ b∈Finset.range (N+1), if k≤b then (1/4:ℝ)^b else 0 := by
      apply Finset.sum_le_sum
      intro b _
      rw [hLaw]
      by_cases hb : k≤b
      · simp only [ite_eq_left hb]
        exact weighted_binomial_probability_le N b q hq hq1 hNq
      · simp only [ite_eq_right hb,zero_mul,le_refl]
    _ ≤ _ := geometric_tail_sum k N

end
end Tournament.Probability
