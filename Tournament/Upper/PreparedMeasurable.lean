module

public import Tournament.Upper.RoundingMeasurable
public import Tournament.Upper.AdaptivePreparation

@[expose] public section

namespace Tournament.HoldingFamily

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

theorem ratio_measurable (H : A → HoldingFamily ι)
    (hp : ∀ i, Measurable (fun a ↦ (H a).sampling i))
    (hx : ∀ i, Measurable (fun a ↦ (H a).refresh i)) (i : ι) :
    Measurable (fun a ↦ (H a).ratio i) := (hx i).div (hp i)

theorem refreshRate_measurable (H : A → HoldingFamily ι)
    (hp : ∀ i, Measurable (fun a ↦ (H a).sampling i))
    (hx : ∀ i, Measurable (fun a ↦ (H a).refresh i)) (τ : ℝ) (i : ι) :
    Measurable (fun a ↦ (H a).refreshRate τ i) := by
  have h : Measurable (fun a ↦ τ*(H a).ratio i) := measurable_const.mul (ratio_measurable H hp hx i)
  exact h.div (measurable_const.mul (measurable_const.add h))

theorem meanRefreshRate_measurable (H : A → HoldingFamily ι)
    (hp : ∀ i, Measurable (fun a ↦ (H a).sampling i))
    (hx : ∀ i, Measurable (fun a ↦ (H a).refresh i)) (τ : ℝ) :
    Measurable (fun a ↦ (H a).meanRefreshRate τ) :=
  Finset.measurable_sum _ (fun i _ ↦ (hp i).mul (refreshRate_measurable H hp hx τ i))

theorem destination_measurable (H : A → HoldingFamily ι)
    (hp : ∀ i, Measurable (fun a ↦ (H a).sampling i))
    (hx : ∀ i, Measurable (fun a ↦ (H a).refresh i)) (τ : ℝ) (hτ : 0<τ) (i : ι) :
    Measurable (fun a ↦ (H a).destination τ hτ i) :=
  ((hp i).mul (refreshRate_measurable H hp hx τ i)).div (meanRefreshRate_measurable H hp hx τ)

theorem kernel_entry_measurable (H : A → HoldingFamily ι)
    (hp : ∀ i, Measurable (fun a ↦ (H a).sampling i))
    (hx : ∀ i, Measurable (fun a ↦ (H a).refresh i)) (τ : ℝ) (hτ : 0<τ) (i j : ι) :
    Measurable (fun a ↦ (H a).kernel τ hτ i j) :=
  ((measurable_const.sub (refreshRate_measurable H hp hx τ i)).mul measurable_const).add
    ((refreshRate_measurable H hp hx τ i).mul (destination_measurable H hp hx τ hτ j))

end
end Tournament.HoldingFamily

namespace Tournament.Upper.ComparisonAssignment

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]
variable {F : ι → ι → Prop} {v : A → ProbabilityVector ι}

theorem preparedSampling_measurable (C : (a : A) → ComparisonAssignment F (v a))
    (hq : ∀ i, Measurable (fun a ↦ (C a).sourceLaw i)) (w : A → ProbabilityVector ι)
    (hw : ∀ i, Measurable (fun a ↦ w a i)) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    Measurable (fun a ↦ (C a).preparedSampling (w a) κ hκ hκ32 i) :=
  (measurable_const.mul (hw i)).add (measurable_const.mul (hq i))

theorem preparedFamily_refresh_measurable (C : (a : A) → ComparisonAssignment F (v a))
    (hq : ∀ i, Measurable (fun a ↦ (C a).sourceLaw i)) (w : A → ProbabilityVector ι)
    (hw : ∀ i, Measurable (fun a ↦ w a i)) (hPos : ∀ a i, 0<w a i)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    Measurable (fun a ↦ ((C a).preparedFamily (w a) (hPos a) κ hκ hκ32).refresh i) :=
  ((preparedSampling_measurable C hq w hw κ hκ hκ32 i).add (hq i)).div_const 2

theorem estimator_measurable (C : (a : A) → ComparisonAssignment F (v a))
    (hC : ∀ s i r, Measurable (fun a ↦ (C a).matrix s i r))
    (w p : A → ProbabilityVector ι) (hw : ∀ i, Measurable (fun a ↦ w a i))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (s i r : ι) :
    Measurable (fun a ↦ (C a).estimator (w a) (p a) s i r) :=
  ((hC s i r).sub (Finset.measurable_sum _ (fun k _ ↦ (hw k).mul (hC s k r)))).div (hp s)

theorem comparisonDecoder_measurable (C : (a : A) → ComparisonAssignment F (v a))
    (hC : ∀ s i r, Measurable (fun a ↦ (C a).matrix s i r))
    (obs : A → ι → ℝ) (hObs : ∀ i, Measurable (fun a ↦ obs a i)) (s i : ι) :
    Measurable (fun a ↦ (C a).comparisonDecoder s (obs a) i) := by
  apply Finset.measurable_sum
  intro r _
  have hEdge : Measurable (fun a ↦ (C a).edgeWeight s i r) := by
    by_cases hir : i=r
    · simp only [edgeWeight,ite_eq_left hir]
      exact measurable_const
    · simp only [edgeWeight,ite_eq_right hir]
      exact (hC s i r).neg
  exact hEdge.mul ((hObs r).sub (hObs i))

def estimatorDecoder {v : ProbabilityVector ι} (C : ComparisonAssignment F v)
    (w p : ProbabilityVector ι) (s : ι) (obs : ι → ℝ) (i : ι) : ℝ :=
  w.center (C.comparisonDecoder s obs) i/p s

omit [MeasurableSpace A] in
theorem estimatorDecoder_observation {v : ProbabilityVector ι} (C : ComparisonAssignment F v)
    (w p : ProbabilityVector ι) (s : ι) (loss : ι → ℝ) (i : ι) :
    C.estimatorDecoder w p s (Model.comparisonObservation F s loss) i=
      applyEstimator (C.estimator w p) s loss i := by
  have hDecode : C.comparisonDecoder s (Model.comparisonObservation F s loss)=C.act s loss :=
    funext (fun k ↦ C.comparisonDecoder_eq s loss k)
  rw [C.estimator_apply]
  simp only [estimatorDecoder,hDecode]

theorem estimatorDecoder_measurable (C : (a : A) → ComparisonAssignment F (v a))
    (hC : ∀ s i r, Measurable (fun a ↦ (C a).matrix s i r))
    (w p : A → ProbabilityVector ι) (hw : ∀ i, Measurable (fun a ↦ w a i))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (obs : A → ι → ℝ)
    (hObs : ∀ i, Measurable (fun a ↦ obs a i)) (s i : ι) :
    Measurable (fun a ↦ (C a).estimatorDecoder (w a) (p a) s (obs a) i) := by
  have hDecode (k : ι) : Measurable (fun a ↦ (C a).comparisonDecoder s (obs a) k) :=
    comparisonDecoder_measurable C hC obs hObs s k
  exact ((hDecode i).sub (Finset.measurable_sum _ (fun k _ ↦ (hw k).mul (hDecode k)))).div (hp s)

end
end Tournament.Upper.ComparisonAssignment

namespace Tournament.Upper.Rounding

open MeasureTheory
open scoped Classical
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]
variable (F : ι → ι → Prop) (hF : IsTournament F)
variable (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
variable (hPos : ∀ a i, 0<p a i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
variable (hFloor : ∀ a i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤p a i) (m : ℕ) (hm : 5≤m)
include hp

theorem rounded_sampling_measurable (i : ι) :
    Measurable (fun a ↦ (roundedHolding F hF (p a) (hPos a) T hK hT (hFloor a) m hm).sampling i) := by
  exact ComparisonAssignment.preparedSampling_measurable _
    (optimized_sourceLaw_measurable F hF p hp T (by omega) (fun a ↦ anchor_pos (p a) hK hT (hFloor a)))
    p hp (DyadicRate.base m) (DyadicRate.base_pos m) (BlockParameters.base_le_one_thirtytwo hm) i

theorem rounded_refresh_measurable (i : ι) :
    Measurable (fun a ↦ (roundedHolding F hF (p a) (hPos a) T hK hT (hFloor a) m hm).refresh i) := by
  exact ComparisonAssignment.preparedFamily_refresh_measurable _
    (optimized_sourceLaw_measurable F hF p hp T (by omega) (fun a ↦ anchor_pos (p a) hK hT (hFloor a)))
    p hp hPos (DyadicRate.base m) (DyadicRate.base_pos m) (BlockParameters.base_le_one_thirtytwo hm) i

theorem rounded_kernel_measurable (τ : ℝ) (hτ : 0<τ) (i j : ι) :
    Measurable (fun a ↦ (roundedHolding F hF (p a) (hPos a) T hK hT (hFloor a) m hm).kernel τ hτ i j) :=
  HoldingFamily.kernel_entry_measurable _
    (rounded_sampling_measurable F hF p hp hPos T hK hT hFloor m hm)
    (rounded_refresh_measurable F hF p hp hPos T hK hT hFloor m hm) τ hτ i j

theorem rounded_estimator_measurable (s i r : ι) :
    Measurable (fun a ↦ roundedEstimator F hF (p a) (hPos a) T hK hT (hFloor a) m hm s i r) :=
  ComparisonAssignment.estimator_measurable _
    (optimized_matrix_measurable F hF p hp T (by omega) (fun a ↦ anchor_pos (p a) hK hT (hFloor a)))
    p _ hp (rounded_sampling_measurable F hF p hp hPos T hK hT hFloor m hm) s i r

end
end Tournament.Upper.Rounding

namespace Tournament.Upper.SteeringParameters

open MeasureTheory
open scoped Classical
noncomputable section

variable {ι A : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace A]

theorem anchor_weight_measurable (S : SteeringParameters ι) (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : ι) :
    Measurable (fun a ↦ S.anchor (p a) i) :=
  (measurable_const.mul (hp i)).add measurable_const

theorem rounded_holding_sampling_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : ι) :
    Measurable (fun a ↦ (S.holding (p a)).sampling i) := by
  simp only [holding,preparation,hRound,ite_true]
  exact Rounding.rounded_sampling_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
    (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) S.T S.card_ge_two S.time_ge_two
    (fun a ↦ S.anchor_floor (p a)) S.m S.bands_ge_five i

theorem rounded_holding_refresh_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : ι) :
    Measurable (fun a ↦ (S.holding (p a)).refresh i) := by
  simp only [holding,preparation,hRound,ite_true]
  exact Rounding.rounded_refresh_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
    (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) S.T S.card_ge_two S.time_ge_two
    (fun a ↦ S.anchor_floor (p a)) S.m S.bands_ge_five i

theorem rounded_holding_kernel_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (τ : ℝ) (hτ : 0<τ) (i j : ι) :
    Measurable (fun a ↦ (S.holding (p a)).kernel τ hτ i j) :=
  HoldingFamily.kernel_entry_measurable (fun a ↦ S.holding (p a))
    (rounded_holding_sampling_measurable S hRound p hp) (rounded_holding_refresh_measurable S hRound p hp) τ hτ i j

theorem rounded_estimator_entry_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (s i r : ι) :
    Measurable (fun a ↦ S.estimator (p a) s i r) := by
  simp only [estimator,preparation,hRound,ite_true]
  exact Rounding.rounded_estimator_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
    (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) S.T S.card_ge_two S.time_ge_two
    (fun a ↦ S.anchor_floor (p a)) S.m S.bands_ge_five s i r

end
end Tournament.Upper.SteeringParameters
