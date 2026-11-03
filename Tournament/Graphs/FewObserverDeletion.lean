module

public import Tournament.Graphs.FewObserverThinning
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

namespace Tournament.ObserverSampling

open scoped Classical BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def heavyMembers (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) (a : ι) : Finset ι :=
  if k≤(observedMembers E X a).card then observedMembers E X a else ∅

def firstDeletion (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) : Finset ι :=
  Finset.univ.biUnion (heavyMembers E k X)

def firstRemainder (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) : Finset ι := X \ firstDeletion E k X

def orderedEdges (E : ι → ι → Prop) (X : Finset ι) : Finset (ι × ι) :=
  X.offDiag.filter (fun p ↦ E p.1 p.2)

def edgeDeletion (E : ι → ι → Prop) (X : Finset ι) : Finset ι := (orderedEdges E X).image Prod.fst

def survivors (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) : Finset ι :=
  firstRemainder E k X \ edgeDeletion E (firstRemainder E k X)

theorem firstDeletion_subset (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) : firstDeletion E k X ⊆ X := by
  intro v hv
  obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hv
  unfold heavyMembers at ha
  split_ifs at ha
  · exact (Finset.mem_filter.mp ha).1
  · simp at ha

theorem survivors_subset (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) : survivors E k X ⊆ X :=
  (Finset.sdiff_subset).trans Finset.sdiff_subset

theorem no_distinct_edges (E : ι → ι → Prop) (k : ℕ) (X : Finset ι)
    (u v : ι) (hu : u∈survivors E k X) (hv : v∈survivors E k X) (hne : u≠v) : ¬ E u v := by
  intro he
  have hu' := Finset.mem_sdiff.mp hu
  have hv' := Finset.mem_sdiff.mp hv
  apply hu'.2
  apply Finset.mem_image.mpr
  exact ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hu'.1,hv'.1,hne⟩,he⟩,rfl⟩

omit [Fintype ι] in
theorem observedMembers_mono (E : ι → ι → Prop) {X Y : Finset ι} (hXY : X ⊆ Y) (a : ι) :
    observedMembers E X a ⊆ observedMembers E Y a := Finset.filter_subset_filter _ hXY

theorem surviving_observer_count (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) (a : ι) :
    (observedMembers E (survivors E k X) a).card≤k-1 := by
  by_cases hHeavy : k≤(observedMembers E X a).card
  · have hEmpty : observedMembers E (survivors E k X) a=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvs := Finset.mem_filter.mp hv
      have hvA := (Finset.mem_sdiff.mp hvs.1).1
      have hvX := survivors_subset E k X hvs.1
      have hvDel : v∈firstDeletion E k X := Finset.mem_biUnion.mpr
        ⟨a,Finset.mem_univ a,by
          rw [heavyMembers,ite_eq_left hHeavy]
          exact Finset.mem_filter.mpr ⟨hvX,hvs.2⟩⟩
      exact (Finset.mem_sdiff.mp hvA).2 hvDel
    rw [hEmpty,Finset.card_empty]
    exact Nat.zero_le _
  · have hCard := Finset.card_le_card (observedMembers_mono E (survivors_subset E k X) a)
    omega

theorem firstDeletion_card_le (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) :
    (firstDeletion E k X).card≤∑ a, if k≤(observedMembers E X a).card then (observedMembers E X a).card else 0 := by
  have h : (firstDeletion E k X).card≤∑ a, (heavyMembers E k X a).card := Finset.card_biUnion_le
  simpa only [heavyMembers,apply_ite,Finset.card_empty] using h

omit [Fintype ι] in
theorem edgeDeletion_card_le (E : ι → ι → Prop) (X : Finset ι) :
    (edgeDeletion E X).card≤(orderedEdges E X).card := Finset.card_image_le

omit [Fintype ι] in
theorem orderedEdges_mono (E : ι → ι → Prop) {X Y : Finset ι} (hXY : X ⊆ Y) :
    orderedEdges E X ⊆ orderedEdges E Y := Finset.filter_subset_filter _ (Finset.offDiag_mono hXY)

theorem deletion_card_bound (E : ι → ι → Prop) (k : ℕ) (X : Finset ι) :
    X.card≤(survivors E k X).card+
      (∑ a, if k≤(observedMembers E X a).card then (observedMembers E X a).card else 0)+(orderedEdges E X).card := by
  have hFirst := Finset.card_le_card_sdiff_add_card (s := X) (t := firstDeletion E k X)
  have hSecond := Finset.card_le_card_sdiff_add_card
    (s := firstRemainder E k X) (t := edgeDeletion E (firstRemainder E k X))
  have hFirstBound := firstDeletion_card_le E k X
  have hEdgeBound := (edgeDeletion_card_le E (firstRemainder E k X)).trans
    (Finset.card_le_card (orderedEdges_mono E (Finset.sdiff_subset (s := X) (t := firstDeletion E k X))))
  change X.card≤(firstRemainder E k X).card+(firstDeletion E k X).card at hFirst
  change (firstRemainder E k X).card≤(survivors E k X).card+(edgeDeletion E (firstRemainder E k X)).card at hSecond
  omega

end
end Tournament.ObserverSampling
