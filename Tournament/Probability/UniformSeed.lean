module

public import Tournament.Probability.KernelSampler

@[expose] public section

namespace Tournament.Probability.UniformSeed

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval
noncomputable section

abbrev Space (n : ℕ) := Fin n → unitInterval

def law (n : ℕ) : Measure (Space n) := Measure.pi (fun _ : Fin n ↦ (volume : Measure unitInterval))

instance law_probability (n : ℕ) : IsProbabilityMeasure (law n) := by unfold law; infer_instance

def take (n B : ℕ) (h : n≤B) (ω : Space B) : Space n := fun i ↦ ω (Fin.castLE h i)

theorem take_measurable (n B : ℕ) (h : n≤B) : Measurable (take n B h) :=
  Measurable.of_eval (fun _ ↦ measurable_pi_apply _)

theorem take_self (n : ℕ) (ω : Space n) : take n n le_rfl ω=ω := by
  funext i
  rfl

theorem take_comp (a b B : ℕ) (hab : a≤b) (hbB : b≤B) (ω : Space B) :
    take a b hab (take b B hbB ω)=take a B (hab.trans hbB) ω := by
  funext i
  rfl

theorem take_init (n B : ℕ) (h : n+1≤B) (ω : Space B) :
    Fin.init (take (n+1) B h ω)=take n B (by omega) ω := by
  funext i
  rfl

theorem take_hasLaw (n B : ℕ) (h : n≤B) : HasLaw (take n B h) (law n) (law B) := by
  have hI : iIndepFun (fun i (ω : Space B) ↦ ω i) (law B) := iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hInj : Function.Injective (Fin.castLE h) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin B ↦ z.val) hij)
  have hRestrict := iIndepFun.precomp hInj hI
  exact hRestrict.hasLaw_pi (fun i ↦
    (measurePreserving_eval (fun _ : Fin B ↦ (volume : Measure unitInterval)) (Fin.castLE h i)).hasLaw)

theorem prefix_fresh_hasLaw (n : ℕ) :
    HasLaw (fun ω : Space (n+1) ↦ (Fin.init ω,ω (Fin.last n)))
      ((law n).prod (volume : Measure unitInterval)) (law (n+1)) := by
  let S : Finset (Fin (n+1)) := Finset.univ.erase (Fin.last n)
  let f : (S → unitInterval) → Space n := fun b j ↦ b ⟨j.castSucc,by simp [S]⟩
  let g : (({Fin.last n} : Finset (Fin (n+1))) → unitInterval) → unitInterval := fun b ↦ b ⟨Fin.last n,by simp⟩
  have hI : iIndepFun (fun i (ω : Space (n+1)) ↦ ω i) (law (n+1)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hDisjoint : Disjoint S ({Fin.last n} : Finset (Fin (n+1))) := by simp [S]
  have hGroups := hI.indepFun_finset S {Fin.last n} hDisjoint (fun _ ↦ measurable_pi_apply _)
  have hf : Measurable f := Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
  have hg : Measurable g := measurable_pi_apply _
  have hIndep := hGroups.comp hf hg
  change IndepFun (fun ω : Space (n+1) ↦ Fin.init ω) (fun ω ↦ ω (Fin.last n)) (law (n+1)) at hIndep
  have hLeft : HasLaw (fun ω : Space (n+1) ↦ Fin.init ω) (law n) (law (n+1)) := by
    convert take_hasLaw n (n+1) (by omega) using 1
    funext ω j
    rfl
  have hRight := (measurePreserving_eval (fun _ : Fin (n+1) ↦ (volume : Measure unitInterval)) (Fin.last n)).hasLaw
  exact hIndep.hasLaw_prod hLeft hRight

end
end Tournament.Probability.UniformSeed
