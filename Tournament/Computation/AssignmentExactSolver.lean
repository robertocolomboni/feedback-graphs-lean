module

public import Tournament.Computation.AssignmentFiniteParser
public import Tournament.Computation.AssignmentFiniteGeometry
public import Tournament.Computation.OptimizerCodeMeasurable

@[expose] public section

namespace Tournament.Computation.AssignmentExactSolver

open Upper AssignmentEncoding AssignmentSerialization AssignmentFiniteGeometry
open LinearProgramming

def solveProgramOption {K : ℕ} (P : Program (Fin K)) : Option (Variable (Fin K) → ℚ) :=
  (FiniteVertexSolver.solve (matrix K P) (rhs K P) (objective K P)).map
    (fun q k => q ((variableEquiv K).symm k))

def solveProgram {K : ℕ} (P : Program (Fin K)) : Variable (Fin K) → ℚ :=
  (solveProgramOption P).getD (fun _ => 0)

def candidate (K : ℕ) : OptimizerCodeMeasurable.Candidate K := fun bits key =>
  match AssignmentFiniteParser.parse K bits with
  | none => 0
  | some P => solveProgram P key

@[simp] theorem candidate_serialized (K : ℕ) (P : Program (Fin K)) :
    candidate K (serialize K P) = solveProgram P := by
  funext k
  simp [candidate]

theorem solveProgram_correct {K : ℕ} (P : Program (Fin K))
    (hcompact : IsCompact (ActiveRows.integerPolyhedron (matrix K P) (rhs K P)))
    (hne : (ActiveRows.integerPolyhedron (matrix K P) (rhs K P)).Nonempty) :
    P.Feasible (fun k => (solveProgram P k : ℝ)) ∧
      ∀ y, P.Feasible y → evaluate P.objective (fun k => (solveProgram P k : ℝ)) ≤
        evaluate P.objective y := by
  obtain ⟨q, hq, hf, hmin⟩ := FiniteVertexSolver.solve_correct (matrix K P) (rhs K P)
    (objective K P) hcompact hne
  have hout : solveProgram P = fun k => q ((variableEquiv K).symm k) := by
    simp [solveProgram, solveProgramOption, hq]
  have hc : (fun k => (solveProgram P k : ℝ)) = coordinates K (FiniteVertexSolver.point q) := by
    funext k
    rw [hout]
    rfl
  rw [hc]
  constructor
  · exact (feasible_iff K P _).mp ((FiniteVertexSolver.feasible_iff _ _ q).mp hf)
  · intro y hy
    let x : EuclideanSpace ℝ (Fin (dimension K)) := WithLp.toLp 2 (fun j => y (variableEquiv K j))
    have hxy : coordinates K x = y := by
      funext k
      simp [coordinates, x]
    have hx : x ∈ ActiveRows.integerPolyhedron (matrix K P) (rhs K P) :=
      (feasible_iff K P x).mpr (hxy.symm ▸ hy)
    have hm := hmin x hx
    rw [objective_eq K P, objective_eq K P, hxy] at hm
    exact hm

theorem rounded_correct (K : ℕ) (F : Fin K → Fin K → Prop) [DecidableRel F]
    (hF : IsTournament F) (w : ProbabilityVector (Fin K)) (T : ℕ) (hK : 2≤K) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((K:ℝ)*(T:ℝ))≤w i) :
    let P := encode F (Rounding.numerator w T) (Rounding.denominator w T)
    let answer := fun k => (candidate K (serialize K P) k : ℝ)
    P.Feasible answer ∧ ∀ y, P.Feasible y → evaluate P.objective answer ≤ evaluate P.objective y := by
  dsimp only
  rw [candidate_serialized]
  obtain ⟨hc, hn⟩ := rounded_compact_nonempty K F hF w T hK hT hwfloor
  exact solveProgram_correct _ hc hn

set_option maxHeartbeats 1200000 in
theorem correctOnRounded {K : ℕ} [Nonempty (Fin K)]
    (S : SteeringParameters (Fin K)) :
    OptimizerCodeMeasurable.CorrectOnRounded S (candidate K) := by
  classical
  have hc (π : ProbabilityVector (Fin K)) := rounded_correct K S.tournament S.isTournament
    (S.anchor π) S.T (by simpa using S.card_ge_two) S.time_ge_two
    (by simpa using S.anchor_floor π)
  have hp (π : ProbabilityVector (Fin K)) : OptimizerCodeMeasurable.program S π =
      encode S.tournament (Rounding.numerator (S.anchor π) S.T) (Rounding.denominator (S.anchor π) S.T) := by
    unfold OptimizerCodeMeasurable.program
    congr 1
    exact Subsingleton.elim _ _
  have hw (π : ProbabilityVector (Fin K)) : OptimizerCodeMeasurable.wireInput S.tournament (S.anchor π) S.T =
      serialize K (encode S.tournament (Rounding.numerator (S.anchor π) S.T) (Rounding.denominator (S.anchor π) S.T)) := by
    unfold OptimizerCodeMeasurable.wireInput
    congr 2
    exact Subsingleton.elim _ _
  have hs (π : ProbabilityVector (Fin K)) : OptimizerCodeMeasurable.solution S (candidate K) π =
      (fun k => (candidate K (serialize K (encode S.tournament (Rounding.numerator (S.anchor π) S.T)
        (Rounding.denominator (S.anchor π) S.T))) k : ℝ)) := by
    unfold OptimizerCodeMeasurable.solution
    rw [hw]
  constructor
  · intro π
    rw [hp, hs]
    exact (hc π).1
  · intro π x hx
    rw [hp, hs]
    exact (hc π).2 x ((hp π) ▸ hx)

end Tournament.Computation.AssignmentExactSolver
