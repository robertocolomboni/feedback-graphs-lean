module

public import Tournament.Computation.AssignmentEncoding
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.ProdSigma

@[expose] public section

namespace Tournament.Computation.AssignmentSerialization

open AssignmentEncoding

def decodeBits : List Bool → ℕ
  | [] => 0
  | b::bs => Nat.bit b (decodeBits bs)

@[simp] theorem decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [decodeBits, ih]

def decodeSigned (sign : Bool) (bits : List Bool) : ℤ :=
  if sign then -(decodeBits bits : ℤ) else (decodeBits bits : ℤ)

@[simp] theorem decodeSigned_integer (z : ℤ) :
    decodeSigned (decide (z<0)) z.natAbs.bits = z := by
  cases z with
  | ofNat n => simp [decodeSigned]
  | negSucc n =>
      simp only [decodeSigned, Int.negSucc_lt_zero, decide_true,
        ite_true, Int.natAbs_negSucc, decodeBits_bits]
      rfl

def frame (z : ℤ) : List Bool :=
  List.replicate z.natAbs.bits.length true ++
    [false, decide (z<0)] ++ z.natAbs.bits

def parseUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::bs => some (0,bs)
  | true::bs => (parseUnary bs).map (fun p => (p.1+1,p.2))

@[simp] theorem parseUnary_delimited (n : ℕ) (bs : List Bool) :
    parseUnary (List.replicate n true ++ false::bs) = some (n,bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, parseUnary, ih]

def parseField (bs : List Bool) : Option (ℤ × List Bool) := do
  let (n, rest) ← parseUnary bs
  match rest with
  | [] => none
  | sign::payload =>
      if n ≤ payload.length then
        some (decodeSigned sign (payload.take n), payload.drop n)
      else none

@[simp] theorem parseField_frame (z : ℤ) (tail : List Bool) :
    parseField (frame z ++ tail) = some (z,tail) := by
  simp [frame, List.append_assoc, parseField]

theorem frame_injective : Function.Injective frame := by
  intro z z' h
  have hp := congrArg parseField (congrArg (fun bs => bs ++ []) h)
  simpa only [parseField_frame, Option.some.injEq, Prod.mk.injEq, and_true] using hp

variable {ι : Type*}

theorem framedField_eq_frame (P : Program ι) (k : AssignmentEncoding.Field ι) :
    P.framedField k = frame (P.field k) := rfl

@[simp] theorem parseField_framedField (P : Program ι) (k : AssignmentEncoding.Field ι) (tail : List Bool) :
    parseField (P.framedField k ++ tail) = some (P.field k, tail) :=
  parseField_frame _ _

theorem program_field_injective : Function.Injective (Program.field (ι := ι)) := by
  intro P Q h
  have hD : P.denominator = Q.denominator := by
    have hd := congrFun h (.inl ())
    change (P.denominator : ℤ) = (Q.denominator : ℤ) at hd
    exact_mod_cast hd
  have heq : P.equalities = Q.equalities := by
    funext row k
    exact congrFun h (.inr (.inl (row,k)))
  have hrhs : P.equalityRhs = Q.equalityRhs := by
    funext row
    exact congrFun h (.inr (.inr (.inl row)))
  have hloads : P.loads = Q.loads := by
    funext row k
    exact congrFun h (.inr (.inr (.inr (.inl (row,k)))))
  have hlo : P.lower = Q.lower := by
    funext k
    exact congrFun h (.inr (.inr (.inr (.inr (.inl k)))))
  have hup : P.upper = Q.upper := by
    funext k
    exact congrFun h (.inr (.inr (.inr (.inr (.inr (.inl k))))))
  have hobj : P.objective = Q.objective := by
    funext k
    exact congrFun h (.inr (.inr (.inr (.inr (.inr (.inr k))))))
  cases P
  cases Q
  simp_all

theorem program_framedFields_injective :
    Function.Injective (fun P : Program ι => P.framedField) := by
  intro P Q h
  apply program_field_injective
  funext k
  exact frame_injective (congrFun h k)

def sumList {α β : Type*} (xs : List α) (ys : List β) : List (α ⊕ β) :=
  xs.map Sum.inl ++ ys.map Sum.inr

@[simp] theorem mem_sumList_left {α β : Type*} (xs : List α) (ys : List β) (x : α) :
    Sum.inl x ∈ sumList xs ys ↔ x ∈ xs := by simp [sumList]

@[simp] theorem mem_sumList_right {α β : Type*} (xs : List α) (ys : List β) (y : β) :
    Sum.inr y ∈ sumList xs ys ↔ y ∈ ys := by simp [sumList]

@[simp] theorem length_sumList {α β : Type*} (xs : List α) (ys : List β) :
    (sumList xs ys).length = xs.length+ys.length := by simp [sumList]

def variableList (K : ℕ) : List (Variable (Fin K)) :=
  sumList ((List.finRange K).product ((List.finRange K).product (List.finRange K)))
    (List.finRange K)

def rowList (K : ℕ) : List (EqualityRow (Fin K)) :=
  sumList ((List.finRange K).product (List.finRange K))
    ((List.finRange K).product (List.finRange K))

def fieldList (K : ℕ) : List (AssignmentEncoding.Field (Fin K)) :=
  sumList [()] (sumList ((rowList K).product (variableList K))
    (sumList (rowList K) (sumList ((rowList K).product (variableList K))
      (sumList (variableList K) (sumList (variableList K) (variableList K))))))

@[simp] theorem mem_variableList (K : ℕ) (v : Variable (Fin K)) : v ∈ variableList K := by
  rcases v with ⟨a,b,c⟩ | a <;> simp [variableList]

@[simp] theorem mem_rowList (K : ℕ) (r : EqualityRow (Fin K)) : r ∈ rowList K := by
  rcases r with ⟨a,b⟩ | ⟨a,b⟩ <;> simp [rowList]

theorem mem_fieldList (K : ℕ) (k : AssignmentEncoding.Field (Fin K)) : k ∈ fieldList K := by
  rcases k with u | (⟨row,k⟩ | (row | (⟨row,k⟩ | (k | (k | k))))) <;>
    simp [fieldList]

theorem listProduct_length {α β : Type*} (xs : List α) (ys : List β) :
    (xs.product ys).length = xs.length*ys.length := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih => simp [List.product, List.flatMap_cons] at ih ⊢; nlinarith

theorem fieldList_length (K : ℕ) : (fieldList K).length =
    1+4*K^2*(K^3+K)+2*K^2+3*(K^3+K) := by
  simp [fieldList, variableList, rowList, listProduct_length]
  ring

def serializeFields (P : Program ι) (ks : List (AssignmentEncoding.Field ι)) : List Bool :=
  ks.flatMap P.framedField

def parseFields : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bs => some ([],bs)
  | n+1, bs => do
      let (z,rest) ← parseField bs
      let (zs,tail) ← parseFields n rest
      some (z::zs,tail)

@[simp] theorem parseFields_serializeFields (P : Program ι)
    (ks : List (AssignmentEncoding.Field ι)) (tail : List Bool) :
    parseFields ks.length (serializeFields P ks ++ tail) = some (ks.map P.field,tail) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [serializeFields, List.flatMap_cons, List.append_assoc, List.length_cons,
      parseFields, parseField_framedField]
    simpa [serializeFields] using congrArg
      (fun out => Option.bind out (fun p => some (P.field k::p.1,p.2))) ih

def serialize (K : ℕ) (P : Program (Fin K)) : List Bool := serializeFields P (fieldList K)

theorem serialize_injective (K : ℕ) : Function.Injective (serialize K) := by
  intro P Q h
  have hh := congrArg (parseFields (fieldList K).length)
    (congrArg (fun bs => bs ++ []) h)
  simp only [serialize, parseFields_serializeFields, Option.some.injEq, Prod.mk.injEq,
    and_true] at hh
  apply program_field_injective
  funext k
  exact List.map_inj_left.mp hh k (mem_fieldList K k)

end Tournament.Computation.AssignmentSerialization
