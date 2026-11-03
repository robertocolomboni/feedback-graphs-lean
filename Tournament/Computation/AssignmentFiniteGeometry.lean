module

public import Tournament.Computation.AssignmentSerialization
public import Tournament.Computation.LinearProgramming.FiniteVertexSolver
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

namespace Tournament.Computation.AssignmentFiniteGeometry

open Tournament.Upper AssignmentEncoding AssignmentSerialization LinearProgramming
open scoped BigOperators

theorem variableList_nodup (K : ℕ) : (variableList K).Nodup := by
  unfold variableList sumList
  refine List.nodup_append.mpr ⟨?_,?_,?_⟩
  · exact ((List.nodup_finRange K).product
      ((List.nodup_finRange K).product (List.nodup_finRange K))).map Sum.inl_injective
  · exact (List.nodup_finRange K).map Sum.inr_injective
  · intro a ha b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    simp

def dimension (K : ℕ) : ℕ := (variableList K).length

def variableEquiv (K : ℕ) : Fin (dimension K) ≃ Variable (Fin K) :=
  List.Nodup.getEquivOfForallMemList (variableList K) (variableList_nodup K) (mem_variableList K)

def pullback (K : ℕ) (a : Variable (Fin K) → ℤ) : Fin (dimension K) → ℤ :=
  fun j => a (variableEquiv K j)

def unitCoefficient (K : ℕ) (D : ℕ) (k : Variable (Fin K)) : Variable (Fin K) → ℤ :=
  fun l => if l=k then (D:ℤ) else 0

def rows (K : ℕ) (P : Program (Fin K)) : List ((Fin (dimension K) → ℤ) × ℤ) :=
  (rowList K).flatMap (fun r =>
    [(pullback K (P.equalities r),P.equalityRhs r),
     (pullback K (fun k => -P.equalities r k),-P.equalityRhs r)]) ++
  (rowList K).map (fun r => (pullback K (P.loads r),0)) ++
  (variableList K).flatMap (fun k =>
    [(pullback K (fun l => -unitCoefficient K P.denominator k l),-P.lower k),
     (pullback K (unitCoefficient K P.denominator k),P.upper k)])

def matrix (K : ℕ) (P : Program (Fin K)) :
    Fin (rows K P).length → Fin (dimension K) → ℤ := fun i => ((rows K P).get i).1

def rhs (K : ℕ) (P : Program (Fin K)) : Fin (rows K P).length → ℤ :=
  fun i => ((rows K P).get i).2

def objective (K : ℕ) (P : Program (Fin K)) : Fin (dimension K) → ℤ :=
  pullback K P.objective

def coordinates (K : ℕ) (x : EuclideanSpace ℝ (Fin (dimension K))) : Variable (Fin K) → ℝ :=
  fun k => x ((variableEquiv K).symm k)

noncomputable def embed (K : ℕ) (x : Variable (Fin K) → ℝ) :
    EuclideanSpace ℝ (Fin (dimension K)) := WithLp.toLp 2 (fun j => x (variableEquiv K j))

@[simp] theorem coordinates_embed (K : ℕ) (x : Variable (Fin K) → ℝ) :
    coordinates K (embed K x) = x := by
  funext k
  exact congrArg x ((variableEquiv K).apply_symm_apply k)

@[simp] theorem coordinates_equiv (K : ℕ) (x : EuclideanSpace ℝ (Fin (dimension K)))
    (j : Fin (dimension K)) : coordinates K x (variableEquiv K j) = x j := by
  exact congrArg x ((variableEquiv K).symm_apply_apply j)

theorem evaluate_pullback (K : ℕ) (a : Variable (Fin K) → ℤ)
    (x : EuclideanSpace ℝ (Fin (dimension K))) :
    (∑ j, (pullback K a j:ℝ)*x j) = evaluate a (coordinates K x) := by
  simpa only [pullback, evaluate, coordinates_equiv] using
    (variableEquiv K).sum_comp (fun k => (a k:ℝ)*coordinates K x k)

theorem evaluate_neg (K : ℕ) (a : Variable (Fin K) → ℤ) (x : Variable (Fin K) → ℝ) :
    evaluate (fun k => -a k) x = -evaluate a x := by
  simp [evaluate, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem evaluate_unit (K D : ℕ) (k : Variable (Fin K)) (x : Variable (Fin K) → ℝ) :
    evaluate (unitCoefficient K D k) x = (D:ℝ)*x k := by
  simp [evaluate,unitCoefficient]

theorem feasible_iff (K : ℕ) (P : Program (Fin K))
    (x : EuclideanSpace ℝ (Fin (dimension K))) :
    x ∈ ActiveRows.integerPolyhedron (matrix K P) (rhs K P) ↔
      P.Feasible (coordinates K x) := by
  have hlist :
      (∀ i : Fin (rows K P).length,
        (∑ j, (((rows K P).get i).1 j:ℝ)*x j) ≤ (((rows K P).get i).2:ℝ)) ↔
      ∀ r ∈ rows K P, (∑ j, (r.1 j:ℝ)*x j) ≤ (r.2:ℝ) := by
    constructor
    · intro h r hr
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
      simpa only [List.get_eq_getElem,he] using h ⟨i,hi⟩
    · intro h i
      exact h _ (List.get_mem _ _)
  simp only [ActiveRows.integerPolyhedron, ActiveRows.polyhedron, Set.mem_ofPred_eq,
    ActiveRows.integerRow, PiLp.inner_apply, real_inner_comm, matrix, rhs]
  change (∀ i : Fin (rows K P).length,
    (∑ j, (((rows K P).get i).1 j:ℝ)*x j) ≤ (((rows K P).get i).2:ℝ)) ↔ _
  rw [hlist]
  simp only [rows,List.forall_mem_append,List.forall_mem_flatMap,
    List.forall_mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,List.forall_mem_map,
    mem_rowList,mem_variableList,evaluate_pullback,evaluate_neg,
    evaluate_unit,Int.cast_neg,Int.cast_zero]
  constructor
  · rintro ⟨⟨he,hl⟩,hb⟩
    refine ⟨?_,hl,?_⟩
    · intro r
      exact le_antisymm (he r).1 (neg_le_neg_iff.mp (he r).2)
    · intro k
      exact ⟨neg_le_neg_iff.mp (hb k).1,(hb k).2⟩
  · rintro ⟨he,hl,hb⟩
    refine ⟨⟨?_,hl⟩,?_⟩
    · intro r
      exact ⟨(he r).le,(congrArg Neg.neg (he r)).le⟩
    · intro k
      exact ⟨neg_le_neg (hb k).1,(hb k).2⟩

theorem objective_eq (K : ℕ) (P : Program (Fin K))
    (x : EuclideanSpace ℝ (Fin (dimension K))) :
    FiniteVertexSolver.realObjective (objective K P) x =
      evaluate P.objective (coordinates K x) := by
  rw [FiniteVertexSolver.realObjective_apply]
  exact evaluate_pullback K P.objective x

theorem encoded_unit_box (K : ℕ) (F : Fin K → Fin K → Prop) [DecidableRel F]
    (nums : Fin K → ℕ) (D : ℕ) (hD : 0<D)
    (x : Variable (Fin K) → ℝ) (hx : (encode F nums D).Feasible x) (k : Variable (Fin K)) :
    -1≤x k ∧ x k≤1 := by
  have hbounds : -(D:ℤ)≤(encode F nums D).lower k ∧ (encode F nums D).upper k≤(D:ℤ) := by
    cases k with
    | inl p =>
        rcases p with ⟨s,i,r⟩
        simp only [encode]
        constructor <;> split <;> omega
    | inr s => simp only [encode]; omega
  have hlo : -(D:ℝ)≤((encode F nums D).lower k:ℝ) := by exact_mod_cast hbounds.1
  have hup : ((encode F nums D).upper k:ℝ)≤(D:ℝ) := by exact_mod_cast hbounds.2
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hb := hx.2.2 k
  change ((encode F nums D).lower k:ℝ)≤(D:ℝ)*x k ∧
    (D:ℝ)*x k≤((encode F nums D).upper k:ℝ) at hb
  constructor <;> nlinarith

theorem encoded_compact (K : ℕ) (F : Fin K → Fin K → Prop) [DecidableRel F]
    (nums : Fin K → ℕ) (D : ℕ) (hD : 0<D) :
    IsCompact (ActiveRows.integerPolyhedron (matrix K (encode F nums D)) (rhs K (encode F nums D))) := by
  apply (isCompact_closedBall (0:EuclideanSpace ℝ (Fin (dimension K))) ((dimension K:ℝ)+1)).of_isClosed_subset
    (CompactOptimum.integerPolyhedron_isClosed _ _)
  intro x hx
  have hf := (feasible_iff K (encode F nums D) x).mp hx
  have hb (j : Fin (dimension K)) : -1≤x j ∧ x j≤1 := by
    simpa only [coordinates_equiv] using
      encoded_unit_box K F nums D hD (coordinates K x) hf (variableEquiv K j)
  have hsq : ‖x‖^2 ≤ (dimension K:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j, (x j)^2) ≤ ∑ _j : Fin (dimension K), (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [(hb j).1,(hb j).2]
      _ = (dimension K:ℝ) := by simp
  have hn : ‖x‖ ≤ (dimension K:ℝ)+1 := by
    nlinarith [norm_nonneg x, (Nat.cast_nonneg (dimension K) : (0:ℝ) ≤ (dimension K:ℝ))]
  simpa only [Metric.mem_closedBall,dist_zero_right] using hn

theorem rounded_compact_nonempty (K : ℕ) (F : Fin K → Fin K → Prop) [DecidableRel F]
    (hF : IsTournament F) (w : ProbabilityVector (Fin K)) (T : ℕ) (hK : 2≤K) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((K:ℝ)*(T:ℝ))≤w i) :
    let P := encode F (Rounding.numerator w T) (Rounding.denominator w T)
    IsCompact (ActiveRows.integerPolyhedron (matrix K P) (rhs K P)) ∧
      (ActiveRows.integerPolyhedron (matrix K P) (rhs K P)).Nonempty := by
  dsimp only
  have hD : 0<Rounding.denominator w T := by
    exact_mod_cast Rounding.denominator_pos w (show 0<T by omega)
  refine ⟨encoded_compact K F _ _ hD,?_⟩
  have hk : 2≤Fintype.card (Fin K) := by simpa using hK
  have hw : ∀ i, 1/((Fintype.card (Fin K):ℝ)*(T:ℝ))≤w i := by simpa using hwfloor
  let v := Rounding.anchor w T (show 0<T by omega)
  have hv : ∀ i,0<v i := Rounding.anchor_pos w hk hT hw
  let A := RootedPivots.randomizedAssignment F hF v hv
  refine ⟨embed K (pack (assignmentData A)),(feasible_iff K _ _).mpr ?_⟩
  rw [coordinates_embed]
  exact (rounded_feasible_iff F w hk hT hw (assignmentData A)).mpr (assignmentData_mem A)

end Tournament.Computation.AssignmentFiniteGeometry
