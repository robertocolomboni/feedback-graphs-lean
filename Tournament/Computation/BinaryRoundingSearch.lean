module

public import Tournament.Computation.AssignmentSerialization

@[expose] public section

namespace Tournament.Computation.BinaryRoundingSearch

open AssignmentSerialization
open scoped Classical

def searchWith (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, pref => pref
  | n+1, pref =>
      searchWith test n (if test ((2*pref+1)*2^n) then 2*pref+1 else 2*pref)

noncomputable def strictTest (x : ℝ) (candidate : ℕ) : Bool :=
  decide ((candidate : ℝ)<x)

noncomputable def search (x : ℝ) (n pref : ℕ) : ℕ :=
  searchWith (strictTest x) n pref

theorem search_correct (x : ℝ) (n pref : ℕ)
    (hlo : ((pref*2^n : ℕ) : ℝ)<x)
    (hhi : x≤(((pref+1)*2^n : ℕ) : ℝ)) :
    (search x n pref : ℝ)<x ∧ x≤(search x n pref+1 : ℕ) := by
  induction n generalizing pref with
  | zero => simpa [search, searchWith] using And.intro hlo hhi
  | succ n ih =>
      by_cases ht : (((2*pref+1)*2^n : ℕ) : ℝ)<x
      · have he : search x (n+1) pref=search x n (2*pref+1) := by
          have ht' := ht
          push_cast at ht'
          simp [search, searchWith, strictTest, ht']
        rw [he]
        apply ih _ ht
        have heq : (2*pref+1+1)*2^n=(pref+1)*2^(n+1) := by
          rw [pow_succ]
          ring
        simpa only [heq] using hhi
      · have he : search x (n+1) pref=search x n (2*pref) := by
          have ht' := ht
          push_cast at ht'
          simp [search, searchWith, strictTest, ht']
        rw [he]
        apply ih
        · have heq : (2*pref)*2^n=pref*2^(n+1) := by
            rw [pow_succ]
            ring
          simpa only [heq] using hlo
        · exact le_of_not_gt ht

theorem decodeBits_lt_pow_length (bs : List Bool) : decodeBits bs<2^bs.length := by
  induction bs with
  | nil => simp [decodeBits]
  | cons b bs ih =>
      cases b <;> simp only [decodeBits, Nat.bit_val, Bool.toNat_false,
        Bool.toNat_true, List.length_cons, pow_succ] <;> omega

noncomputable def ceilFromBound (x : ℝ) (bound : ℕ) : ℕ :=
  search x bound.bits.length 0+1

theorem ceilFromBound_correct (x : ℝ) (bound : ℕ)
    (hx : 0<x) (hbound : x≤(bound : ℝ)) : ceilFromBound x bound=⌈x⌉₊ := by
  have hw : bound<2^bound.bits.length := by
    simpa using decodeBits_lt_pow_length bound.bits
  have hupper : x≤((2^bound.bits.length : ℕ) : ℝ) :=
    hbound.trans (by exact_mod_cast hw.le)
  have hs := search_correct x bound.bits.length 0
    (by simpa using hx) (by simpa using hupper)
  unfold ceilFromBound
  apply Nat.le_antisymm
  · have hlt : search x bound.bits.length 0<⌈x⌉₊ := Nat.lt_ceil.mpr hs.1
    omega
  · exact Nat.ceil_le.mpr hs.2

noncomputable def roundWeight (bound : ℕ) (w : ℝ) : ℕ :=
  ceilFromBound ((bound : ℝ)*w) bound

theorem roundWeight_correct (bound : ℕ) (w : ℝ)
    (hB : 0<bound) (hw : 0<w) (hw1 : w≤1) :
    roundWeight bound w=⌈(bound : ℝ)*w⌉₊ := by
  apply ceilFromBound_correct
  · exact mul_pos (by exact_mod_cast hB) hw
  · simpa using mul_le_mul_of_nonneg_left hw1 (Nat.cast_nonneg bound)

theorem paper_numerator (K T : ℕ) (w : ProbabilityVector (Fin K)) (i : Fin K)
    (hK : 0<K) (hT : 0<T) (hw : 0<w i) :
    roundWeight (4*K*T) (w i)=Upper.Rounding.numerator w T i := by
  rw [roundWeight_correct _ _ (by positivity) hw (w.weight_le_one i)]
  simp only [Upper.Rounding.numerator, Upper.Rounding.scale, Fintype.card_fin]

end Tournament.Computation.BinaryRoundingSearch
