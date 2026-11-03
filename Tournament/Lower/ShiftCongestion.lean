module

public import Tournament.Lower.ShiftEnergy
public import Tournament.Lower.DyadicSwitches
public import Tournament.Lower.Parameters

@[expose] public section

namespace Tournament.Lower

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*}

def outsideCount (S : Finset ι) (T : ℕ) (I : ℕ → ι) : ℕ :=
  ∑ t∈Finset.range T, if I t∈S then 0 else 1

def timeShift (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ) (j : Coordinate S)
    (I : ℕ → ι) (sign : ℕ → ℝ) (t : ℕ) : Coordinate S → ℝ :=
  if t=0 then 0 else shift E θ j (I (t-1)) (sign (t-1))

theorem time_shift_energy_le (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (I : ℕ → ι) (sign : ℕ → ℝ)
    (hsign : ∀ t, (sign t)^2=1) (t : ℕ) :
    (∑ j : S, shiftEnergy (timeShift E θ (some j) I sign t))≤(m:ℝ)*θ^2 := by
  by_cases ht : t=0
  · simp only [timeShift,ite_eq_left ht,shiftEnergy,Pi.zero_apply,zero_pow (by decide : 2≠0),
      Finset.sum_const_zero]
    positivity
  · simp only [timeShift,ite_eq_right ht]
    rw [shift_energy_sum E θ _ _ (hsign (t-1))]
    have h := hm (I (t-1))
    have hr : ((observed E S (I (t-1))).card:ℝ)≤(m:ℝ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg θ)]

theorem time_shift_difference_le (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (I : ℕ → ι) (sign : ℕ → ℝ)
    (hsign : ∀ t, (sign t)^2=1) (s t : ℕ) :
    (∑ j : S, shiftEnergy (timeShift E θ (some j) I sign t-timeShift E θ (some j) I sign s))
      ≤4*(m:ℝ)*θ^2 := by
  calc
    _ ≤ ∑ j : S, (2*shiftEnergy (timeShift E θ (some j) I sign t)+
        2*shiftEnergy (timeShift E θ (some j) I sign s)) := by
      apply Finset.sum_le_sum
      intro j _
      exact shiftEnergy_sub_le _ _
    _ = 2*(∑ j : S, shiftEnergy (timeShift E θ (some j) I sign t))+
        2*(∑ j : S, shiftEnergy (timeShift E θ (some j) I sign s)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ _ := by
      have ht := time_shift_energy_le E θ m hm I sign hsign t
      have hs := time_shift_energy_le E θ m hm I sign hsign s
      linarith

theorem time_same_member_shift (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (j : Coordinate S) (I : ℕ → ι) (sign : ℕ → ℝ) (s t : ℕ) (hs : s≠0) (ht : t≠0)
    (heq : Dyadic.padded I t=Dyadic.padded I s) (hmem : I (t-1)∈S) :
    timeShift E θ j I sign t=timeShift E θ j I sign s := by
  have hI : I (t-1)=I (s-1) := by
    simpa only [Dyadic.padded,ite_eq_right ht,ite_eq_right hs,Option.some.injEq] using heq
  simp only [timeShift,ite_eq_right ht,ite_eq_right hs]
  rw [← hI]
  exact same_member_shift E θ j hmem _ _

theorem time_shift_edge_charge (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (I : ℕ → ι) (sign : ℕ → ℝ)
    (hsign : ∀ t, (sign t)^2=1) (s t : ℕ) (ht : 0<t) :
    (∑ j : S, shiftEnergy (timeShift E θ (some j) I sign t-timeShift E θ (some j) I sign s))
      ≤4*(m:ℝ)*θ^2*((Dyadic.changed (Dyadic.padded I) s t:ℝ)+
        (if I (t-1)∈S then 0 else 1)) := by
  have hbound := time_shift_difference_le E θ m hm I sign hsign s t
  by_cases heq : Dyadic.padded I t=Dyadic.padded I s
  · have hs : s≠0 := by
      intro hs
      simp [Dyadic.padded,hs,Nat.ne_of_gt ht] at heq
    by_cases hmem : I (t-1)∈S
    · have hz : ∀ j : S, timeShift E θ (some j) I sign t-timeShift E θ (some j) I sign s=0 := by
        intro j
        rw [time_same_member_shift E θ (some j) I sign s t hs (Nat.ne_of_gt ht) heq hmem,sub_self]
      simp only [hz]
      simp [shiftEnergy,Dyadic.changed,heq,hmem]
    · simpa only [Dyadic.changed,ite_eq_left heq,Nat.cast_zero,ite_eq_right hmem,zero_add,mul_one] using hbound
  · have hnonneg : 0≤4*(m:ℝ)*θ^2 := by positivity
    simp only [Dyadic.changed,ite_eq_right heq,Nat.cast_one]
    split_ifs <;> nlinarith

theorem outsideCount_one_based (S : Finset ι) (T : ℕ) (I : ℕ → ι) :
    (∑ t∈Finset.Icc 1 T, if I (t-1)∈S then (0:ℕ) else 1)=outsideCount S T I := by
  unfold outsideCount
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega : 1≤T+1),ih]
    simp only [Nat.add_sub_cancel]

theorem shift_congestion (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (I : ℕ → ι) (sign : ℕ → ℝ)
    (hsign : ∀ t, (sign t)^2=1) (T : ℕ) (hT : 1≤T) :
    (∑ t∈Finset.Icc 1 T, ∑ j : S,
      shiftEnergy (timeShift E θ (some j) I sign t-timeShift E θ (some j) I sign (Dyadic.parent t)))
      ≤4*(m:ℝ)*θ^2*(Dyadic.upsilon T*((Model.switchCount T I:ℝ)+1)+(outsideCount S T I:ℝ)) := by
  calc
    _ ≤ ∑ t∈Finset.Icc 1 T, 4*(m:ℝ)*θ^2*
        ((Dyadic.changed (Dyadic.padded I) (Dyadic.parent t) t:ℝ)+
          (if I (t-1)∈S then 0 else 1)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact time_shift_edge_charge E θ m hm I sign hsign _ t (by have := (Finset.mem_Icc.mp ht).1; omega)
    _ = 4*(m:ℝ)*θ^2*
        (((∑ t∈Finset.Icc 1 T, Dyadic.changed (Dyadic.padded I) (Dyadic.parent t) t):ℕ)+
          (outsideCount S T I:ℝ)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      push_cast
      congr 1
      have ho := outsideCount_one_based S T I
      exact_mod_cast ho
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · have h := Dyadic.parent_changes_le_switchCount I T hT
        simpa only [Nat.cast_sum] using add_le_add h (le_refl (outsideCount S T I:ℝ))
      · positivity

theorem shift_congestion_source (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (I : ℕ → ι) (sign : ℕ → ℝ)
    (hsign : ∀ t, (sign t)^2=1) (T : ℕ) (hT : 1≤T) :
    (∑ t∈Finset.Icc 1 T, ∑ j : S,
      shiftEnergy (timeShift E θ (some j) I sign t-timeShift E θ (some j) I sign (Dyadic.parent t)))
      ≤4*(m:ℝ)*θ^2*Dyadic.upsilon T*
        ((Model.switchCount T I:ℝ)+(outsideCount S T I:ℝ)+1) := by
  have h := shift_congestion E θ m hm I sign hsign T hT
  have hU := Parameters.upsilon_ge_one T hT
  have ho : 0≤(outsideCount S T I:ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hU ho
  calc
    _ ≤ 4*(m:ℝ)*θ^2*(Dyadic.upsilon T*((Model.switchCount T I:ℝ)+1)+(outsideCount S T I:ℝ)) := h
    _ ≤ 4*(m:ℝ)*θ^2*(Dyadic.upsilon T*((Model.switchCount T I:ℝ)+(outsideCount S T I:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · positivity
    _ = _ := by ring

end
end Tournament.Lower
