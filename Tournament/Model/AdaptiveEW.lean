module

public import Tournament.Probability.ProcessConditional
public import Tournament.Upper.ExpectedEW

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess
open Upper.ExponentialWeights

noncomputable section

universe u v

structure AdaptiveEW (Y : ℕ → Type u) (ι : Type v) [∀ b, Fintype (Y b)] [Fintype ι] where
  rate : ℝ
  output : (b : ℕ) → ProbabilityVector ι → Y b → ι → ℝ
  row : (b : ℕ) → ProbabilityVector ι → ProbabilityVector (Y b)

namespace AdaptiveEW

variable {Y : ℕ → Type u} {ι : Type v} [∀ b, Fintype (Y b)] [Fintype ι] [Nonempty ι]

def distribution (P : AdaptiveEW Y ι) : (b : ℕ) → History Y b → ProbabilityVector ι
  | 0, _ => uniform
  | b+1, x => exponentialUpdate (P.distribution b x.1) P.rate
      (P.output b (P.distribution b x.1) x.2)

def kernel (P : AdaptiveEW Y ι) (b : ℕ) (x : History Y b) : ProbabilityVector (Y b) :=
  P.row b (P.distribution b x)

def execution (P : AdaptiveEW Y ι) (B : ℕ) : ProbabilityVector (History Y B) := law P.kernel B

def blockEstimate (P : AdaptiveEW Y ι) (b : ℕ) (x : History Y (b+1)) : ι → ℝ :=
  P.output b (P.distribution b x.1) x.2

def estimates (P : AdaptiveEW Y ι) (B b : ℕ) (x : History Y B) : ι → ℝ :=
  if h : b<B then P.blockEstimate b (past (b+1) B (by omega) x) else 0

def current (P : AdaptiveEW Y ι) (B b : ℕ) (x : History Y B) : ProbabilityVector ι :=
  if h : b≤B then P.distribution b (past b B h x) else uniform

abbrev histories (B b : ℕ) : MeasurableSpace (History Y B) :=
  information (min b B) B (min_le_right b B)

theorem current_of_le (P : AdaptiveEW Y ι) (B b : ℕ) (h : b≤B) (x : History Y B) :
    P.current B b x=P.distribution b (past b B h x) := by
  simp only [current,dite_eq_left h]

omit [∀ b, Fintype (Y b)] [Fintype ι] [Nonempty ι] in
theorem histories_of_le (B b : ℕ) (h : b≤B) :
    histories (Y := Y) B b=information b B h := by
  simp only [histories,min_eq_left h]

theorem estimates_of_lt (P : AdaptiveEW Y ι) (B b : ℕ) (h : b<B) (x : History Y B) :
    P.estimates B b x=P.blockEstimate b (past (b+1) B (by omega) x) := by
  simp only [estimates,dite_eq_left h]

omit [∀ b, Fintype (Y b)] in
theorem past_next_first (b B : ℕ) (h : b+1≤B) (x : History Y B) :
    (past (b+1) B h x).1=past b B (by omega) x := by
  have hp := past_comp b (b+1) B (by omega) h x
  simpa only [past_succ b b le_rfl,past_self] using hp

theorem weights_eq_distribution (P : AdaptiveEW Y ι) (b B : ℕ) (h : b≤B) (x : History Y B) :
    weights P.rate (P.estimates B) b x=P.distribution b (past b B h x) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hb : b<B := by omega
    change exponentialUpdate (weights P.rate (P.estimates B) b x) P.rate (P.estimates B b x)=_
    rw [ih (by omega),estimates_of_lt P B b hb x]
    change exponentialUpdate (P.distribution b (past b B (by omega) x)) P.rate
      (P.blockEstimate b (past (b+1) B h x))=
        exponentialUpdate (P.distribution b (past (b+1) B h x).1) P.rate
          (P.blockEstimate b (past (b+1) B h x))
    rw [past_next_first b B h x]

theorem weights_eq_current (P : AdaptiveEW Y ι) (b B : ℕ) (h : b≤B) (x : History Y B) :
    weights P.rate (P.estimates B) b x=P.current B b x := by
  rw [current_of_le P B b h x]
  exact weights_eq_distribution P b B h x

theorem estimates_adapted (P : AdaptiveEW Y ι) (b B : ℕ) (hb : b≤B)
    (t : ℕ) (ht : t<b) (i : ι) :
    AEStronglyMeasurable[information b B hb] (fun x ↦ P.estimates B t x i)
      (P.execution B).toMeasure := by
  have htB : t<B := by omega
  have hf := measurable_past_value (t+1) b B (by omega) hb
    (fun s ↦ P.blockEstimate t s i)
  have heq : (fun x ↦ P.estimates B t x i)=
      (fun x ↦ P.blockEstimate t (past (t+1) B (by omega) x) i) :=
    funext (fun x ↦ congrFun (estimates_of_lt P B t htB x) i)
  rw [heq]
  exact hf.stronglyMeasurable.aestronglyMeasurable

theorem condExp_estimate (P : AdaptiveEW Y ι) (b B : ℕ) (h : b<B) (i : ι) :
    (P.execution B).toMeasure[fun x ↦ P.estimates B b x i | information b B (by omega)]
      =ᵐ[(P.execution B).toMeasure] fun x ↦
        (P.row b (P.distribution b (past b B (by omega) x))).mean
          (fun y ↦ P.output b (P.distribution b (past b B (by omega) x)) y i) := by
  have heq : (fun x ↦ P.estimates B b x i)=
      (fun x ↦ P.blockEstimate b (past (b+1) B (by omega) x) i) :=
    funext (fun x ↦ congrFun (estimates_of_lt P B b h x) i)
  rw [heq]
  exact condExp_next P.kernel b B (by omega) (fun s ↦ P.blockEstimate b s i)

end AdaptiveEW
end
end Tournament.Model
