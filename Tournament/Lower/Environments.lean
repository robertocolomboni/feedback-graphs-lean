module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Lower

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*}

abbrev Coordinate (S : Finset ι) := Option S

def observed (E : ι → ι → Prop) (S : Finset ι) (a : ι) : Finset ι := S.filter (E a)

def SparseMembers (E : ι → ι → Prop) (S : Finset ι) : Prop :=
  ∀ a∈S, (observed E S a).card≤1

theorem observed_unique {E : ι → ι → Prop} {S : Finset ι} (hS : SparseMembers E S)
    {a u v : ι} (ha : a∈S) (hu : u∈S) (hv : v∈S) (hau : E a u) (hav : E a v) : u=v :=
  Finset.card_le_one.mp (hS a ha) u (Finset.mem_filter.mpr ⟨hu,hau⟩)
    v (Finset.mem_filter.mpr ⟨hv,hav⟩)

def clip (z : ℝ) : ℝ := min (3/4) (max (1/4) z)

theorem clip_bounds (z : ℝ) : 1/4≤clip z ∧ clip z≤3/4 := by
  unfold clip
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem clip_continuous : Continuous clip := by
  unfold clip
  fun_prop

def rawLoss {S : Finset ι} (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (v : S) : ℝ :=
  1/2+x none+sign*x (some v)-θ*(if j=some v then 1 else 0)

def environmentLoss {S : Finset ι} (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (a : ι) : ℝ :=
  if ha : a∈S then clip (rawLoss θ j sign x ⟨a,ha⟩) else 1

theorem environmentLoss_bounds {S : Finset ι} (θ : ℝ) (j : Coordinate S)
    (sign : ℝ) (x : Coordinate S → ℝ) (a : ι) :
    0≤environmentLoss θ j sign x a ∧ environmentLoss θ j sign x a≤1 := by
  unfold environmentLoss
  split_ifs with ha
  · have h := clip_bounds (rawLoss θ j sign x ⟨a,ha⟩)
    constructor <;> linarith
  · norm_num

theorem outside_gap {S : Finset ι} (θ : ℝ) (j : Coordinate S)
    (sign : ℝ) (x : Coordinate S → ℝ) {a : ι} (ha : a∉S) (v : S) :
    1/4≤environmentLoss θ j sign x a-environmentLoss θ j sign x v := by
  simp only [environmentLoss,dite_eq_right ha,dite_eq_left v.property]
  have h := (clip_bounds (rawLoss θ j sign x v)).2
  linarith

theorem raw_gap {S : Finset ι} (θ : ℝ) (j : Coordinate S) (sign : ℝ)
    (x : Coordinate S → ℝ) (u v : S) :
    rawLoss θ j sign x u-rawLoss θ j sign x v=
      sign*(x (some u)-x (some v))+θ*((if j=some v then 1 else 0)-(if j=some u then 1 else 0)) := by
  unfold rawLoss
  ring

def observesCandidate (E : ι → ι → Prop) {S : Finset ι} (a : ι) : Coordinate S → Prop
  | none => False
  | some j => E a j

def shift (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ) (j : Coordinate S)
    (a : ι) (sign : ℝ) (c : Coordinate S) : ℝ :=
  if a∈S then
    if c=none ∧ observesCandidate E a j then -θ else 0
  else
    if c=j ∧ observesCandidate E a j then -sign*θ else 0

def augmented (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ) (j : Coordinate S)
    (a : ι) (sign : ℝ) (x : Coordinate S → ℝ) : Coordinate S → ℝ :=
  x+shift E θ j a sign

theorem shift_reference (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ) (a : ι) (sign : ℝ) :
    shift E (S := S) θ none a sign=0 := by
  funext c
  simp [shift,observesCandidate]

theorem observesCandidate_iff {E : ι → ι → Prop} {S : Finset ι} (hS : SparseMembers E S)
    {a : ι} (ha : a∈S) (v : S) (hav : E a v) (j : Coordinate S) :
    observesCandidate E a j ↔ j=some v := by
  cases j with
  | none => simp [observesCandidate]
  | some u =>
    constructor
    · intro hu
      have huv : u=v := Subtype.ext (observed_unique hS ha u.property v.property hu hav)
      exact congrArg some huv
    · intro huv
      have h := Option.some.inj huv
      subst u
      exact hav

theorem shift_member_common {E : ι → ι → Prop} {S : Finset ι} (hS : SparseMembers E S)
    (θ : ℝ) {a : ι} (ha : a∈S) (v : S) (hav : E a v) (j : Coordinate S) (sign : ℝ) :
    shift E θ j a sign none= -θ*(if j=some v then 1 else 0) := by
  simp only [shift,ite_eq_left ha,true_and,observesCandidate_iff hS ha v hav j]
  split_ifs <;> ring

theorem shift_member_coordinate {E : ι → ι → Prop} {S : Finset ι}
    (θ : ℝ) {a : ι} (ha : a∈S) (v : S) (j : Coordinate S) (sign : ℝ) :
    shift E θ j a sign (some v)=0 := by
  simp [shift,ha]

theorem shift_outside_common {E : ι → ι → Prop} {S : Finset ι}
    (θ : ℝ) {a : ι} (ha : a∉S) (j : Coordinate S) (sign : ℝ) :
    shift E θ j a sign none=0 := by
  cases j <;> simp [shift,ha,observesCandidate]

theorem shift_outside_coordinate {E : ι → ι → Prop} {S : Finset ι}
    (θ : ℝ) {a : ι} (ha : a∉S) (v : S) (hav : E a v) (j : Coordinate S) (sign : ℝ) :
    shift E θ j a sign (some v)= -sign*θ*(if j=some v then 1 else 0) := by
  by_cases hj : j=some v
  · subst j
    simp [shift,ha,observesCandidate,hav]
  · have hne : some v≠j := Ne.symm hj
    simp [shift,ha,hne,hj]

def memberDecoder {S : Finset ι} (v : S) (sign : ℝ) (o : Coordinate S → ℝ) : ℝ :=
  clip (1/2+o none+sign*o (some v))

theorem memberDecoder_continuous {S : Finset ι} (v : S) :
    Continuous (fun p : ℝ × (Coordinate S → ℝ) ↦ memberDecoder v p.1 p.2) := by
  unfold memberDecoder
  exact clip_continuous.comp (by fun_prop)

theorem reconstruction {E : ι → ι → Prop} {S : Finset ι} (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (a : ι) (sign : ℝ) (hsign : sign^2=1)
    (x : Coordinate S → ℝ) (v : S) (hav : E a v) :
    memberDecoder v sign (augmented E θ j a sign x)=environmentLoss θ j sign x v := by
  simp only [environmentLoss,dite_eq_left v.property,memberDecoder,augmented,Pi.add_apply]
  apply congrArg clip
  by_cases ha : a∈S
  · rw [shift_member_common hS θ ha v hav j sign,shift_member_coordinate θ ha v j sign]
    unfold rawLoss
    ring
  · rw [shift_outside_common θ ha j sign,shift_outside_coordinate θ ha v hav j sign]
    unfold rawLoss
    calc
      _ = 1/2+x none+sign*x (some v)-sign^2*θ*(if j=some v then 1 else 0) := by ring
      _ = _ := by rw [hsign]; ring

def feedbackDecoder (E : ι → ι → Prop) (S : Finset ι) (a : ι)
    (sign : ℝ) (o : Coordinate S → ℝ) (v : ι) : ℝ :=
  if E a v then if hv : v∈S then memberDecoder ⟨v,hv⟩ sign o else 1 else 0

theorem feedbackDecoder_continuous (E : ι → ι → Prop) (S : Finset ι) (a : ι) :
    Continuous (fun p : ℝ × (Coordinate S → ℝ) ↦ feedbackDecoder E S a p.1 p.2) := by
  apply continuous_pi
  intro v
  by_cases he : E a v
  · by_cases hv : v∈S
    · simpa only [feedbackDecoder,ite_eq_left he,dite_eq_left hv] using memberDecoder_continuous (⟨v,hv⟩ : S)
    · simp only [feedbackDecoder,ite_eq_left he,dite_eq_right hv]
      exact continuous_const
  · simp only [feedbackDecoder,ite_eq_right he]
    exact continuous_const

theorem feedback_reconstruction {E : ι → ι → Prop} {S : Finset ι} (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (a : ι) (sign : ℝ) (hsign : sign^2=1)
    (x : Coordinate S → ℝ) (v : ι) :
    feedbackDecoder E S a sign (augmented E θ j a sign x) v=
      if E a v then environmentLoss θ j sign x v else 0 := by
  by_cases he : E a v
  · by_cases hv : v∈S
    · simp only [feedbackDecoder,ite_eq_left he,dite_eq_left hv]
      exact reconstruction hS θ j a sign hsign x ⟨v,hv⟩ he
    · simp [feedbackDecoder,environmentLoss,he,hv]
  · simp [feedbackDecoder,he]

end
end Tournament.Lower
