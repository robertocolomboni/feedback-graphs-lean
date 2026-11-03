module

public import Tournament.Probability.ConditionalRows
public import Tournament.Probability.FiniteProcess
public import Tournament.Probability.FiniteReindex

@[expose] public section

namespace Tournament.ConditionalExecution

open scoped Classical
open ConditionalRows

noncomputable section

universe u
variable {Meta ι : Type u}

def Draw (Meta ι : Type u) : ℕ → Type u
  | 0 => Meta × ι
  | _+1 => ι

instance drawFintype [Fintype Meta] [Fintype ι] (t : ℕ) : Fintype (Draw Meta ι t) := by
  cases t <;> dsimp [Draw] <;> infer_instance

instance drawNonempty [Nonempty Meta] [Nonempty ι] (t : ℕ) : Nonempty (Draw Meta ι t) := by
  cases t <;> dsimp [Draw] <;> infer_instance

def encode : (t : ℕ) → FiniteProcess.History (Draw Meta ι) (t+1) → Meta × (Fin (t+1) → ι)
  | 0, x => (x.2.1, fun _ ↦ x.2.2)
  | t+1, x => ((encode t x.1).1, Fin.snoc (encode t x.1).2 x.2)

def decode : (t : ℕ) → Meta × (Fin (t+1) → ι) → FiniteProcess.History (Draw Meta ι) (t+1)
  | 0, (q,a) => (ULift.up (), (q,a 0))
  | t+1, (q,a) => (decode t (q,Fin.init a), a (Fin.last (t+1)))

theorem decode_encode (t : ℕ) (x : FiniteProcess.History (Draw Meta ι) (t+1)) :
    decode t (encode t x) = x := by
  induction t with
  | zero =>
    rcases x with ⟨⟨⟨⟩⟩,q,i⟩
    rfl
  | succ t ih =>
    rcases x with ⟨h,i⟩
    have hs : Fin.init (Fin.snoc (encode t h).2 (i : ι) : Fin (t+1+1) → ι) =
        (encode t h).2 := @Fin.init_snoc (t+1) (fun _ ↦ ι) i (encode t h).2
    have hl : (Fin.snoc (encode t h).2 (i : ι) : Fin (t+1+1) → ι)
        (Fin.last (t+1)) = i := @Fin.snoc_last (t+1) (fun _ ↦ ι) i (encode t h).2
    change (decode t ((encode t h).1,
      Fin.init (Fin.snoc (encode t h).2 (i : ι) : Fin (t+1+1) → ι)),
      (Fin.snoc (encode t h).2 (i : ι) : Fin (t+1+1) → ι) (Fin.last (t+1))) = (h,i)
    rw [hs, hl]
    change (decode t (encode t h),i) = (h,i)
    rw [ih h]

theorem encode_decode (t : ℕ) (x : Meta × (Fin (t+1) → ι)) :
    encode t (decode t x) = x := by
  induction t with
  | zero =>
    apply Prod.ext
    · rfl
    · funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ t ih =>
    change ((encode t (decode t (x.1,Fin.init x.2))).1,
      Fin.snoc (encode t (decode t (x.1,Fin.init x.2))).2 (x.2 (Fin.last (t+1)))) = x
    rw [ih]
    exact congrArg (fun a ↦ (x.1,a)) (Fin.snoc_init_self x.2)

def historyEquiv (t : ℕ) :
    FiniteProcess.History (Draw Meta ι) (t+1) ≃ Meta × (Fin (t+1) → ι) where
  toFun := encode t
  invFun := decode t
  left_inv := decode_encode t
  right_inv := encode_decode t

variable [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι] {T : ℕ}

def row (μ : ProbabilityVector (Meta × (Fin T → ι))) :
    (t : ℕ) → FiniteProcess.History (Draw Meta ι) t → ProbabilityVector (Draw Meta ι t)
  | 0, _ => if hT : 0 < T then firstRow μ hT else Upper.ExponentialWeights.uniform
  | t+1, x => if ht : t+1 < T then
      nextRow μ (t+1) ht (encode t x).1 (encode t x).2
    else Upper.ExponentialWeights.uniform

theorem law_atom_eq_prefixMass (μ : ProbabilityVector (Meta × (Fin T → ι)))
    (t : ℕ) (ht : t+1 ≤ T) (x : FiniteProcess.History (Draw Meta ι) (t+1)) :
    FiniteProcess.law (row μ) (t+1) x =
      prefixMass μ (t+1) ht (encode t x).1 (encode t x).2 := by
  induction t with
  | zero =>
    have hT : 0 < T := by omega
    change (1 : ℝ) * (row μ 0 x.1) x.2 = _
    rw [one_mul]
    have hr : row μ 0 x.1 = firstRow μ hT := by
      change (if h : 0 < T then firstRow μ h else Upper.ExponentialWeights.uniform) = firstRow μ hT
      split
      · rfl
      · omega
    rw [hr]
    exact firstRow_apply μ hT x.2.1 x.2.2
  | succ t ih =>
    have ht' : t+1 < T := by omega
    change FiniteProcess.law (row μ) (t+1) x.1 * (row μ (t+1) x.1) x.2 = _
    rw [ih (by omega) x.1]
    simp only [row, dite_eq_left ht', encode]
    exact mass_mul_nextRow μ (t+1) ht' (encode t x.1).1 (encode t x.1).2 x.2

theorem law_atom_eq (μ : ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (x : FiniteProcess.History (Draw Meta ι) (T+1)) :
    FiniteProcess.law (row μ) (T+1) x = μ (encode T x) := by
  rw [law_atom_eq_prefixMass μ T le_rfl x, prefixMass_full]

theorem law_decoded_atom_eq (μ : ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (x : Meta × (Fin (T+1) → ι)) :
    FiniteProcess.law (row μ) (T+1) (decode T x) = μ x := by
  rw [law_atom_eq, encode_decode]

theorem law_reindex_eq (μ : ProbabilityVector (Meta × (Fin (T+1) → ι))) :
    (FiniteProcess.law (row μ) (T+1)).reindex (historyEquiv T) = μ := by
  apply ProbabilityVector.ext_weights
  intro x
  exact law_decoded_atom_eq μ x

theorem law_mean_encode (μ : ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (f : Meta × (Fin (T+1) → ι) → ℝ) :
    (FiniteProcess.law (row μ) (T+1)).mean (fun h ↦ f (encode T h)) = μ.mean f := by
  change (FiniteProcess.law (row μ) (T+1)).mean (fun h ↦ f (historyEquiv T h)) = _
  rw [← ProbabilityVector.reindex_mean _ (historyEquiv T) f, law_reindex_eq]

end
end Tournament.ConditionalExecution
