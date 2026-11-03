module

public import Tournament.Computation.BinaryRoundingSearch
public import Tournament.Computation.AssignmentExactSolver

@[expose] public section

namespace Tournament.Computation.FinitePreparation

open Upper BlockParameters AssignmentEncoding AssignmentSerialization
open scoped BigOperators Classical

noncomputable section

variable {K : ℕ}

def numerators (T : ℕ) (w : Fin K → ℝ) : Fin K → ℕ :=
  fun i => BinaryRoundingSearch.roundWeight (4*K*T) (w i)

def wireInput (F : Fin K → Fin K → Prop) [DecidableRel F]
    (T : ℕ) (w : Fin K → ℝ) : List Bool :=
  let n := numerators T w
  serialize K (encode F n (∑ i, n i))

theorem numerators_eq (T : ℕ) (w : ProbabilityVector (Fin K))
    (hK : 0<K) (hT : 0<T) (hw : ∀ i, 0<w i) :
    numerators T w=Rounding.numerator w T := by
  funext i
  exact BinaryRoundingSearch.paper_numerator K T w i hK hT (hw i)

theorem wireInput_eq (F : Fin K → Fin K → Prop) [DecidableRel F]
    (T : ℕ) (w : ProbabilityVector (Fin K))
    (hK : 0<K) (hT : 0<T) (hw : ∀ i, 0<w i) :
    wireInput F T w=OptimizerCodeMeasurable.wireInput F w T := by
  unfold wireInput OptimizerCodeMeasurable.wireInput
  rw [numerators_eq T w hK hT hw]
  dsimp only
  congr 2
  exact Subsingleton.elim _ _

def data (F : Fin K → Fin K → Prop) [DecidableRel F]
    (T : ℕ) (w : Fin K → ℝ) : AssignmentData (Fin K) :=
  unpack (fun v => (AssignmentExactSolver.candidate K (wireInput F T w) v : ℝ))

structure Output (K : ℕ) where
  assignment : AssignmentData (Fin K)
  sampling : Fin K → ℝ
  refresh : Fin K → ℝ
  estimator : Fin K → Fin K → Fin K → ℝ

def finish (d : AssignmentData (Fin K)) (w : Fin K → ℝ) (κ : ℝ) : Output K :=
  let q : Fin K → ℝ := fun i => d.2 i / ∑ j, d.2 j
  let p : Fin K → ℝ := fun i => (1-4*κ)*w i+4*κ*q i
  let x : Fin K → ℝ := fun i => (p i+q i)/2
  let Ψ : Fin K → Fin K → Fin K → ℝ :=
    fun s i r => (d.1 s i r-∑ k, w k*d.1 s k r)/p s
  ⟨d,p,x,Ψ⟩

def prepare (F : Fin K → Fin K → Prop) [DecidableRel F]
    (T : ℕ) (w : Fin K → ℝ) (κ : ℝ) : Output K :=
  finish (data F T w) w κ

theorem finish_correct {F : Fin K → Fin K → Prop} {v : ProbabilityVector (Fin K)}
    (A : ComparisonAssignment F v) (w : ProbabilityVector (Fin K))
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    let out := finish (assignmentData A) w κ
    let H := A.preparedFamily w hw κ hκ hκ32
    out.assignment=assignmentData A ∧ out.sampling=H.sampling ∧
      out.refresh=H.refresh ∧ out.estimator=A.estimator w H.sampling := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem data_correct (F : Fin K → Fin K → Prop) [DecidableRel F]
    (hF : IsTournament F) (T : ℕ) (w : ProbabilityVector (Fin K))
    (hK : 2≤K) (hT : 2≤T) (hwfloor : ∀ i, 1/((K:ℝ)*(T:ℝ))≤w i) :
    let P := encode F (Rounding.numerator w T) (Rounding.denominator w T)
    P.Feasible (pack (data F T w)) ∧ ∀ y, P.Feasible y →
      evaluate P.objective (pack (data F T w))≤evaluate P.objective y := by
  have hw (i : Fin K) : 0<w i :=
    lt_of_lt_of_le (by positivity) (hwfloor i)
  dsimp only
  unfold data
  rw [pack_unpack]
  unfold wireInput
  rw [numerators_eq T w (by omega) (by omega) hw]
  exact AssignmentExactSolver.rounded_correct K F hF w T hK hT hwfloor

theorem prepare_correct (F : Fin K → Fin K → Prop) [DecidableRel F]
    (hF : IsTournament F) (T : ℕ) (w : ProbabilityVector (Fin K))
    (hK : 2≤K) (hT : 2≤T) (hwfloor : ∀ i, 1/((K:ℝ)*(T:ℝ))≤w i)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    ∃ A : ComparisonAssignment F (Rounding.anchor w T (by omega)),
      (∀ B : ComparisonAssignment F (Rounding.anchor w T (by omega)), A.totalWeight≤B.totalWeight) ∧
      (prepare F T w κ).assignment=assignmentData A ∧
      (prepare F T w κ).sampling=(A.preparedFamily w
        (fun i => lt_of_lt_of_le (by positivity) (hwfloor i)) κ hκ hκ32).sampling ∧
      (prepare F T w κ).refresh=(A.preparedFamily w
        (fun i => lt_of_lt_of_le (by positivity) (hwfloor i)) κ hκ hκ32).refresh ∧
      (prepare F T w κ).estimator=A.estimator w (A.preparedFamily w
        (fun i => lt_of_lt_of_le (by positivity) (hwfloor i)) κ hκ hκ32).sampling := by
  let d := data F T w
  have hKd : 2≤Fintype.card (Fin K) := by simpa using hK
  have hw (i : Fin K) : 0<w i := lt_of_lt_of_le (by positivity) (hwfloor i)
  have hc := data_correct F hF T w hK hT hwfloor
  have hd : d ∈ feasibleData F (Rounding.anchor w T (by omega)) :=
    (AssignmentEncoding.rounded_feasible_iff F w hKd hT (by simpa using hwfloor) d).mp hc.1
  let A := assignmentOfData F (Rounding.anchor w T (by omega))
    (Rounding.anchor_pos w hKd hT (by simpa using hwfloor)) d hd
  have hopt (B : ComparisonAssignment F (Rounding.anchor w T (by omega))) :
      A.totalWeight≤B.totalWeight := by
    have hB := (AssignmentEncoding.rounded_feasible_iff F w hKd hT
      (by simpa using hwfloor) (assignmentData B)).mpr (assignmentData_mem B)
    have ho := hc.2 (pack (assignmentData B)) hB
    rw [AssignmentEncoding.objective_eq, AssignmentEncoding.objective_eq] at ho
    exact ho
  refine ⟨A,hopt,?_⟩
  exact finish_correct A w hw κ hκ hκ32

section PaperBlock

local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b => Classical.propDecidable (a=b)

theorem prepared_block_guarantee (F : Fin K → Fin K → Prop) [DecidableRel F]
    (hF : IsTournament F) (w : ProbabilityVector (Fin K)) (hw : ∀ i, 0<w i) (T : ℕ)
    (hK : 2≤K) (hT : 2≤T) (hwfloor : ∀ i, 1/((K:ℝ)*(T:ℝ))≤w i)
    (m : ℕ) (hm : 5≤m) (loss : ℕ → Fin K → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : Fin K) (offset n : ℕ)
    (hn : n+1≤horizon m) :
    ∃ A : ComparisonAssignment F (Rounding.anchor w T (by omega)),
      let H := A.preparedFamily w hw (DyadicRate.base m) (DyadicRate.base_pos m)
        (base_le_one_thirtytwo hm)
      let R : DyadicScoreRules H F m := fun j =>
        tournamentScoreRule F hF _ _ H.sampling_pos
          (H.kernel_reversible (DyadicRate.rate_pos m j))
          (H.kernel_holding_ge_half (DyadicRate.rate_pos m j))
      let out := prepare F T w (DyadicRate.base m)
      out.assignment=assignmentData A ∧ out.sampling=H.sampling ∧
      out.refresh=H.refresh ∧ out.estimator=A.estimator w H.sampling ∧
      OneBlockGuarantee (dyadicBlockLaw H m R loss hloss (threshold K T)
        (threshold_ge_one hK hT) offset n)
        w (blockLoss (fun t => loss (offset+t)) (n+1))
        (dyadicBlockCorrectedEstimate H m R (A.estimator w H.sampling)
          loss (threshold K T) offset n)
        (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  rcases prepare_correct F hF T w hK hT hwfloor (DyadicRate.base m)
    (DyadicRate.base_pos m) (base_le_one_thirtytwo hm) with ⟨A,ho,ha,hp,hx,hΨ⟩
  refine ⟨A,ha,hp,hx,hΨ,?_⟩
  simpa only [Fintype.card_fin] using
    OptimizerTransfer.rounded_block_guarantee_for_optimizer F hF w hw T
      (by simpa using hK) hT (by simpa using hwfloor) m hm A ho loss hloss default offset n hn

end PaperBlock

variable [Nonempty (Fin K)]

theorem data_parameters (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    data S.tournament S.T (S.anchor π)=
      OptimizerCodeMeasurable.data S (AssignmentExactSolver.candidate K) π := by
  unfold data OptimizerCodeMeasurable.data OptimizerCodeMeasurable.solution
  rw [wireInput_eq S.tournament S.T (S.anchor π)
    (by have := S.card_ge_two; simpa using (show 0<Fintype.card (Fin K) by omega))
    (by have := S.time_ge_two; omega) (S.anchor_pos π)]

theorem prepare_parameters (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    let solve := AssignmentExactSolver.candidate K
    let h := AssignmentExactSolver.correctOnRounded S
    let A := OptimizerCodeMeasurable.assignment S solve h π
    let P := OptimizerCodeMeasurable.parameters S solve h
    let out := prepare S.tournament S.T (S.anchor π) (DyadicRate.base S.m)
    out.assignment=assignmentData A ∧ out.sampling=(P.holding π).sampling ∧
      out.refresh=(P.holding π).refresh ∧ out.estimator=P.estimator π := by
  dsimp only
  unfold prepare
  rw [data_parameters S π]
  exact finish_correct
    (OptimizerCodeMeasurable.assignment S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S) π)
    (S.anchor π) (S.anchor_pos π) (DyadicRate.base S.m) (DyadicRate.base_pos S.m)
    (BlockParameters.base_le_one_thirtytwo S.bands_ge_five)

end
end Tournament.Computation.FinitePreparation
