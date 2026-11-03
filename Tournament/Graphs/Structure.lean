module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Tournament

variable {ι : Type*}

def StronglyRevealing (E : ι → ι → Prop) : Prop :=
  ∀ i j, i ≠ j → (E i i ∧ E i j) ∨ (E j j ∧ E j i)

def StronglyObservable (E : ι → ι → Prop) : Prop :=
  ∀ i, E i i ∨ ∀ j, j ≠ i → E j i

def BanditPair (E : ι → ι → Prop) (i j : ι) : Prop :=
  i ≠ j ∧ E i i ∧ E j j ∧ ¬ E i j ∧ ¬ E j i

def LooplessPair (E : ι → ι → Prop) (i j : ι) : Prop :=
  i ≠ j ∧ ¬ E i i ∧ ¬ E j j ∧ E i j ∧ E j i

theorem stronglyRevealing_implies_stronglyObservable
    {E : ι → ι → Prop} (h : StronglyRevealing E) : StronglyObservable E := by
  classical
  intro i
  by_cases hii : E i i
  · exact Or.inl hii
  · right
    intro j hji
    rcases h i j (Ne.symm hji) with hi | hj
    · exact False.elim (hii hi.1)
    · exact hj.2

theorem stronglyRevealing_no_banditPair
    {E : ι → ι → Prop} (h : StronglyRevealing E) (i j : ι) :
    ¬ BanditPair E i j := by
  rintro ⟨hij, _, _, hnij, hnji⟩
  rcases h i j hij with hi | hj
  · exact hnij hi.2
  · exact hnji hj.2

theorem stronglyRevealing_no_looplessPair
    {E : ι → ι → Prop} (h : StronglyRevealing E) (i j : ι) :
    ¬ LooplessPair E i j := by
  rintro ⟨hij, hnii, hnjj, _, _⟩
  rcases h i j hij with hi | hj
  · exact hnii hi.1
  · exact hnjj hj.1

theorem stronglyRevealing_iff_no_forbidden_pairs
    {E : ι → ι → Prop} (hobs : StronglyObservable E) :
    StronglyRevealing E ↔
      (∀ i j, ¬ BanditPair E i j) ∧ (∀ i j, ¬ LooplessPair E i j) := by
  classical
  constructor
  · intro h
    exact ⟨stronglyRevealing_no_banditPair h, stronglyRevealing_no_looplessPair h⟩
  · rintro ⟨hbandit, hloopless⟩ i j hij
    by_cases hii : E i i
    · by_cases hjj : E j j
      · by_cases he : E i j
        · exact Or.inl ⟨hii, he⟩
        · by_cases he' : E j i
          · exact Or.inr ⟨hjj, he'⟩
          · exact False.elim (hbandit i j ⟨hij, hii, hjj, he, he'⟩)
      · rcases hobs j with hjj' | hj
        · exact False.elim (hjj hjj')
        · exact Or.inl ⟨hii, hj i hij⟩
    · by_cases hjj : E j j
      · rcases hobs i with hii' | hi
        · exact False.elim (hii hii')
        · exact Or.inr ⟨hjj, hi j (Ne.symm hij)⟩
      · have heij : E i j := (hobs j).resolve_left hjj i hij
        have heji : E j i := (hobs i).resolve_left hii j (Ne.symm hij)
        exact False.elim (hloopless i j ⟨hij, hii, hjj, heij, heji⟩)

def IsTournament (F : ι → ι → Prop) : Prop :=
  ∀ i j, i ≠ j → (F i j ∨ F j i) ∧ ¬ (F i j ∧ F j i)

section Orientation

variable [LinearOrder ι]

def selectedEdge (E : ι → ι → Prop) (i j : ι) : Prop :=
  if i = j then E i i
  else (E i i ∧ E i j) ∧ (¬ (E j j ∧ E j i) ∨ i < j)

@[simp] theorem selectedEdge_self (E : ι → ι → Prop) (i : ι) :
    selectedEdge E i i ↔ E i i := by
  simp [selectedEdge]

theorem selectedEdge_ne (E : ι → ι → Prop) {i j : ι} (hij : i ≠ j) :
    selectedEdge E i j ↔ (E i i ∧ E i j) ∧ (¬ (E j j ∧ E j i) ∨ i < j) := by
  simp [selectedEdge, hij]

theorem selectedEdge_subgraph (E : ι → ι → Prop) {i j : ι}
    (h : selectedEdge E i j) : E i j := by
  by_cases hij : i = j
  · subst j
    exact (selectedEdge_self E i).mp h
  · exact ((selectedEdge_ne E hij).mp h).1.2

theorem selectedEdge_source_loop (E : ι → ι → Prop) {i j : ι}
    (h : selectedEdge E i j) : selectedEdge E i i := by
  by_cases hij : i = j
  · subst j
    exact h
  · exact (selectedEdge_self E i).mpr ((selectedEdge_ne E hij).mp h).1.1

theorem selectedEdge_isTournament {E : ι → ι → Prop}
    (h : StronglyRevealing E) : IsTournament (selectedEdge E) := by
  classical
  intro i j hij
  constructor
  · rcases h i j hij with hi | hj
    · by_cases hj : E j j ∧ E j i
      · rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact Or.inl ((selectedEdge_ne E hij).mpr ⟨hi, Or.inr hlt⟩)
        · exact Or.inr ((selectedEdge_ne E (Ne.symm hij)).mpr ⟨hj, Or.inr hlt⟩)
      · exact Or.inl ((selectedEdge_ne E hij).mpr ⟨hi, Or.inl hj⟩)
    · by_cases hi : E i i ∧ E i j
      · rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact Or.inl ((selectedEdge_ne E hij).mpr ⟨hi, Or.inr hlt⟩)
        · exact Or.inr ((selectedEdge_ne E (Ne.symm hij)).mpr ⟨hj, Or.inr hlt⟩)
      · exact Or.inr ((selectedEdge_ne E (Ne.symm hij)).mpr ⟨hj, Or.inl hi⟩)
  · rintro ⟨hij', hji'⟩
    rcases (selectedEdge_ne E hij).mp hij' with ⟨hi, horder⟩
    rcases (selectedEdge_ne E (Ne.symm hij)).mp hji' with ⟨hj, horder'⟩
    rcases horder with hnot | hlt
    · exact hnot hj
    · rcases horder' with hnot | hlt'
      · exact hnot hi
      · exact lt_asymm hlt hlt'

theorem selectedEdge_stronglyObservable {E : ι → ι → Prop}
    (h : StronglyRevealing E) : StronglyObservable (selectedEdge E) := by
  classical
  intro i
  by_cases hii : selectedEdge E i i
  · exact Or.inl hii
  · right
    intro j hji
    rcases (selectedEdge_isTournament h i j (Ne.symm hji)).1 with hij' | hji'
    · exact False.elim (hii (selectedEdge_source_loop E hij'))
    · exact hji'

end Orientation

theorem stronglyObservable_tournament_source_loop {F : ι → ι → Prop}
    (ht : IsTournament F) (ho : StronglyObservable F) {i j : ι}
    (hij : i ≠ j) (he : F i j) : F i i := by
  classical
  by_contra hn
  have hji : F j i := (ho i).resolve_left hn j (Ne.symm hij)
  exact (ht i j hij).2 ⟨he, hji⟩

theorem stronglyRevealing_iff_spanning_tournament [LinearOrder ι]
    (E : ι → ι → Prop) :
    StronglyRevealing E ↔ ∃ F : ι → ι → Prop,
      (∀ i j, F i j → E i j) ∧ IsTournament F ∧ StronglyObservable F := by
  constructor
  · intro h
    exact ⟨selectedEdge E, fun _ _ he ↦ selectedEdge_subgraph E he,
      selectedEdge_isTournament h, selectedEdge_stronglyObservable h⟩
  · rintro ⟨F, hsub, ht, ho⟩ i j hij
    rcases (ht i j hij).1 with he | he
    · exact Or.inl ⟨hsub i i (stronglyObservable_tournament_source_loop ht ho hij he),
        hsub i j he⟩
    · exact Or.inr ⟨hsub j j (stronglyObservable_tournament_source_loop ht ho (Ne.symm hij) he),
        hsub j i he⟩

end Tournament
