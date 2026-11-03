module

public import Tournament.Computation.AssignmentSerialization

@[expose] public section

namespace Tournament.Computation.AssignmentFiniteParser

open AssignmentEncoding AssignmentSerialization

set_option synthInstance.maxSize 2048 in
instance fieldDecidableEq (K : ℕ) : DecidableEq (AssignmentEncoding.Field (Fin K)) := by
  unfold AssignmentEncoding.Field EqualityRow LoadRow Variable
  infer_instance

def readTable {α : Type*} [DecidableEq α] : List α → List ℤ → α → ℤ
  | [], _, _ => 0
  | _::_, [], _ => 0
  | k::ks, z::zs, a => if a=k then z else readTable ks zs a

theorem readTable_map {α : Type*} [DecidableEq α] (keys : List α) (f : α → ℤ)
    (a : α) (ha : a ∈ keys) : readTable keys (keys.map f) a = f a := by
  induction keys with
  | nil => simp at ha
  | cons k ks ih =>
      by_cases h : a=k
      · subst a
        simp [readTable]
      · simp only [List.mem_cons] at ha
        simp only [List.map_cons, readTable, h, ↓reduceIte]
        exact ih (ha.resolve_left h)

def fromFields (K : ℕ) (values : List ℤ) : Program (Fin K) :=
  let get := readTable (fieldList K) values
  { denominator := (get (.inl ())).toNat
    equalities := fun r k => get (.inr (.inl (r,k)))
    equalityRhs := fun r => get (.inr (.inr (.inl r)))
    loads := fun r k => get (.inr (.inr (.inr (.inl (r,k)))))
    lower := fun k => get (.inr (.inr (.inr (.inr (.inl k)))))
    upper := fun k => get (.inr (.inr (.inr (.inr (.inr (.inl k))))))
    objective := fun k => get (.inr (.inr (.inr (.inr (.inr (.inr k)))))) }

@[simp] theorem fromFields_program (K : ℕ) (P : Program (Fin K)) :
    fromFields K ((fieldList K).map P.field) = P := by
  have hr (a : AssignmentEncoding.Field (Fin K)) :=
    readTable_map (fieldList K) P.field a (mem_fieldList K a)
  cases P
  simp only [fromFields, hr, Program.field, Int.toNat_natCast]

def parse (K : ℕ) (bits : List Bool) : Option (Program (Fin K)) := do
  let (values, rest) ← parseFields (fieldList K).length bits
  if rest=[] then some (fromFields K values) else none

@[simp] theorem parse_serialize (K : ℕ) (P : Program (Fin K)) :
    parse K (serialize K P) = some P := by
  have hp := parseFields_serializeFields P (fieldList K) []
  simp only [List.append_nil] at hp
  simp [parse, serialize, hp]

end Tournament.Computation.AssignmentFiniteParser
