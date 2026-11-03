module

public import Tournament.Upper.AssignmentOptimum
public import Tournament.Upper.Rounding
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace Tournament.Computation.AssignmentEncoding

open Tournament.Upper
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Variable (ι : Type*) := (ι × ι × ι) ⊕ ι
abbrev EqualityRow (ι : Type*) := (ι × ι) ⊕ (ι × ι)
abbrev LoadRow (ι : Type*) := (ι × ι) ⊕ (ι × ι)

structure Program (ι : Type*) where
  denominator : ℕ
  equalities : EqualityRow ι → Variable ι → ℤ
  equalityRhs : EqualityRow ι → ℤ
  loads : LoadRow ι → Variable ι → ℤ
  lower : Variable ι → ℤ
  upper : Variable ι → ℤ
  objective : Variable ι → ℤ

def allowed (F : ι → ι → Prop) [DecidableRel F] (s i r : ι) : Prop :=
  (i = s ∨ F s i) ∧ (r = s ∨ F s r)

instance allowedDecidable (F : ι → ι → Prop) [DecidableRel F] (s i r : ι) :
    Decidable (allowed F s i r) := inferInstanceAs (Decidable ((_ ∨ _) ∧ (_ ∨ _)))

def encode (F : ι → ι → Prop) [DecidableRel F] (n : ι → ℕ) (D : ℕ) : Program ι where
  denominator := D
  equalities row k := match row, k with
    | .inl (s,i), .inl (a,b,_) => if a=s ∧ b=i then D else 0
    | .inr (i,r), .inl (_,b,c) => if b=i ∧ c=r then D else 0
    | _, .inr _ => 0
  equalityRhs row := match row with
    | .inl _ => 0
    | .inr (i,r) => (if i=r then (D:ℤ) else 0) - n r
  loads row k := match row, k with
    | .inl (s,i), .inl (a,b,c) => if a=s ∧ b=i ∧ c=i then D else 0
    | .inl (s,_), .inr a => if a=s then -(D:ℤ) else 0
    | .inr (s,i), .inl (a,b,c) => if a=s ∧ b=i ∧ c=i then n i else 0
    | .inr (s,i), .inr a => if a=i then -(n s:ℤ) else 0
  lower k := match k with
    | .inl (s,i,r) => if allowed F s i r then -(D:ℤ) else 0
    | .inr s => n s
  upper k := match k with
    | .inl (s,i,r) => if allowed F s i r ∧ i=r then D else 0
    | .inr _ => D
  objective k := match k with
    | .inl _ => 0
    | .inr _ => 1

def pack (d : AssignmentData ι) : Variable ι → ℝ
  | .inl (s,i,r) => d.1 s i r
  | .inr s => d.2 s

def unpack (x : Variable ι → ℝ) : AssignmentData ι :=
  (fun s i r => x (.inl (s,i,r)), fun s => x (.inr s))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem unpack_pack (d : AssignmentData ι) : unpack (pack d) = d := by
  cases d
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pack_unpack (x : Variable ι → ℝ) : pack (unpack x) = x := by
  funext k
  cases k <;> rfl

noncomputable def evaluate (a : Variable ι → ℤ) (x : Variable ι → ℝ) : ℝ :=
  ∑ k, (a k : ℝ) * x k

def Program.Feasible (P : Program ι) (x : Variable ι → ℝ) : Prop :=
  (∀ row, evaluate (P.equalities row) x = (P.equalityRhs row : ℝ)) ∧
  (∀ row, evaluate (P.loads row) x ≤ 0) ∧
  (∀ k, (P.lower k : ℝ) ≤ (P.denominator : ℝ)*x k ∧
    (P.denominator : ℝ)*x k ≤ (P.upper k : ℝ))

theorem equality_row_sum (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (d : AssignmentData ι) (s i : ι) :
    evaluate ((encode F n D).equalities (.inl (s,i))) (pack d) =
      (D:ℝ) * ∑ r, d.1 s i r := by
  simp [evaluate, encode, pack, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ite_and, ← Finset.mul_sum]

theorem equality_total (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (d : AssignmentData ι) (i r : ι) :
    evaluate ((encode F n D).equalities (.inr (i,r))) (pack d) =
      (D:ℝ) * ∑ s, d.1 s i r := by
  simp [evaluate, encode, pack, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ite_and, ← Finset.mul_sum]

theorem load_source (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (d : AssignmentData ι) (s i : ι) :
    evaluate ((encode F n D).loads (.inl (s,i))) (pack d) =
      (D:ℝ) * d.1 s i i - (D:ℝ) * d.2 s := by
  simp [evaluate, encode, pack, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ite_and, sub_eq_add_neg]

theorem load_balanced (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (d : AssignmentData ι) (s i : ι) :
    evaluate ((encode F n D).loads (.inr (s,i))) (pack d) =
      (n i:ℝ) * d.1 s i i - (n s:ℝ) * d.2 i := by
  simp [evaluate, encode, pack, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ite_and, sub_eq_add_neg]

theorem objective_eq (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (d : AssignmentData ι) :
    evaluate (encode F n D).objective (pack d) = assignmentObjective d := by
  simp [evaluate, encode, pack, assignmentObjective, Fintype.sum_sum_type]

theorem feasible_iff (F : ι → ι → Prop) [DecidableRel F]
    (n : ι → ℕ) (D : ℕ) (hD : 0 < D) (v : ProbabilityVector ι)
    (hv : ∀ i, 0 < v i) (hanchor : ∀ i, (D:ℝ)*v i = n i)
    (d : AssignmentData ι) :
    (encode F n D).Feasible (pack d) ↔ d ∈ feasibleData F v := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  constructor
  · rintro ⟨heq,hload,hbounds⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro s i
      have h := heq (.inl (s,i))
      rw [equality_row_sum] at h
      simp only [encode, Int.cast_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hDR)
    · intro s i r hir
      have h := (hbounds (.inl (s,i,r))).2
      simp [encode, pack, hir] at h
      nlinarith
    · intro s i r hs
      have hs' : ¬ allowed F s i r := hs
      have h := hbounds (.inl (s,i,r))
      simp [encode, pack, hs'] at h
      nlinarith [h.1,h.2]
    · intro i r
      have h := heq (.inr (i,r))
      rw [equality_total] at h
      apply mul_left_cancel₀ (ne_of_gt hDR)
      rw [mul_sub, hanchor r]
      by_cases hir : i=r <;> simpa [encode, hir] using h
    · intro s i
      have h := hload (.inl (s,i))
      rw [load_source] at h
      nlinarith
    · intro s i
      have h := hload (.inr (s,i))
      rw [load_balanced] at h
      have hscale : (D:ℝ)*(v i*d.1 s i i - v s*d.2 i) =
          (n i:ℝ)*d.1 s i i - (n s:ℝ)*d.2 i := by
        rw [mul_sub, ← mul_assoc, ← mul_assoc, hanchor i, hanchor s]
      have hz : v i*d.1 s i i - v s*d.2 i ≤ 0 := by nlinarith
      linarith
    · intro s
      have h := (hbounds (.inr s)).1
      simp only [encode, pack, Int.cast_natCast] at h
      rw [← hanchor s] at h
      nlinarith
    · intro s
      have h := (hbounds (.inr s)).2
      simp only [encode, pack, Int.cast_natCast] at h
      nlinarith
  · intro hd
    let A := assignmentOfData F v hv d hd
    refine ⟨?_,?_,?_⟩
    · intro row
      rcases row with ⟨s,i⟩ | ⟨i,r⟩
      · rw [equality_row_sum]
        simp only [encode, Int.cast_zero]
        change (D:ℝ)*(∑ r, A.matrix s i r)=0
        rw [A.row_sum, mul_zero]
      · rw [equality_total]
        change (D:ℝ)*(∑ s, A.matrix s i r)=_
        rw [A.total_matrix, mul_sub, hanchor r]
        by_cases hir : i=r <;> simp [encode, hir]
    · intro row
      rcases row with ⟨s,i⟩ | ⟨s,i⟩
      · rw [load_source]
        have h := A.load_le_source s i
        change d.1 s i i ≤ d.2 s at h
        nlinarith
      · rw [load_balanced]
        have h := A.balanced_load s i
        change v i*d.1 s i i ≤ v s*d.2 i at h
        calc
          (n i:ℝ)*d.1 s i i - (n s:ℝ)*d.2 i =
              (D:ℝ)*(v i*d.1 s i i - v s*d.2 i) := by
            rw [mul_sub, ← mul_assoc, ← mul_assoc, hanchor i, hanchor s]
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDR.le (sub_nonpos.mpr h)
    · intro k
      rcases k with ⟨s,i,r⟩ | s
      · by_cases hs : allowed F s i r
        · have hb := A.entry_bounds s i r
          change -1 ≤ d.1 s i r ∧ d.1 s i r ≤ 1 at hb
          by_cases hir : i=r
          · subst r
            simp only [encode, pack, hs, and_self, ite_true, Int.cast_neg,
              Int.cast_natCast]
            constructor <;> nlinarith [hb.1,hb.2]
          · have ho := A.offdiag_nonpos s i r hir
            change d.1 s i r ≤ 0 at ho
            simp only [encode, pack, hs, hir, and_false, ite_true, ite_false,
              Int.cast_neg, Int.cast_natCast, Int.cast_zero]
            constructor <;> nlinarith [hb.1]
        · have hzero : d.1 s i r=0 := A.support s i r hs
          simp [encode, pack, hs, hzero]
      · have hlo := A.anchor_le_source s
        have hup := A.source_le_one s
        change v s ≤ d.2 s at hlo
        change d.2 s ≤ 1 at hup
        simp only [encode, pack, Int.cast_natCast]
        rw [← hanchor s]
        constructor <;> nlinarith

abbrev Field (ι : Type*) := Unit ⊕ ((EqualityRow ι × Variable ι) ⊕
  (EqualityRow ι ⊕ ((LoadRow ι × Variable ι) ⊕
  (Variable ι ⊕ (Variable ι ⊕ Variable ι)))))

def Program.field (P : Program ι) : Field ι → ℤ
  | .inl _ => P.denominator
  | .inr (.inl (row,k)) => P.equalities row k
  | .inr (.inr (.inl row)) => P.equalityRhs row
  | .inr (.inr (.inr (.inl (row,k)))) => P.loads row k
  | .inr (.inr (.inr (.inr (.inl k)))) => P.lower k
  | .inr (.inr (.inr (.inr (.inr (.inl k))))) => P.upper k
  | .inr (.inr (.inr (.inr (.inr (.inr k))))) => P.objective k

def Program.binaryField (P : Program ι) (k : Field ι) : Bool × List Bool :=
  (decide (P.field k < 0), (P.field k).natAbs.bits)

def Program.framedField (P : Program ι) (k : Field ι) : List Bool :=
  List.replicate (P.binaryField k).2.length true ++
    [false, (P.binaryField k).1] ++ (P.binaryField k).2

theorem rounded_feasible_iff (F : ι → ι → Prop) [DecidableRel F]
    (w : ProbabilityVector ι) {T : ℕ} (hK : 2 ≤ Fintype.card ι) (hT : 2 ≤ T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ)) ≤ w i)
    (d : AssignmentData ι) :
    (encode F (Rounding.numerator w T) (Rounding.denominator w T)).Feasible (pack d) ↔
      d ∈ feasibleData F (Rounding.anchor w T (by omega)) := by
  have hD := Rounding.denominator_pos w (show 0<T by omega)
  apply feasible_iff F _ _ (by exact_mod_cast hD) _
    (Rounding.anchor_pos w hK hT hwfloor)
  intro i
  change (Rounding.denominator w T:ℝ) *
    ((Rounding.numerator w T i:ℝ)/(Rounding.denominator w T:ℝ)) = _
  field_simp [ne_of_gt hD]

end Tournament.Computation.AssignmentEncoding
