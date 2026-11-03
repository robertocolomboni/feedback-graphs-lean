module

public import Tournament.Upper.GeneratorInverse
public import Tournament.Upper.RateComparison

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

def synthesize (H : HoldingFamily ι) (a : H.CenteredIndex → ℝ) (i : ι) : ℝ :=
  ∑ n, a n*H.eigenvector n i

theorem synthesize_centered (H : HoldingFamily ι) (a : H.CenteredIndex → ℝ) :
    H.sampling.mean (H.synthesize a)=0 := by
  unfold synthesize
  rw [ProbabilityVector.mean_sum]
  simp only [ProbabilityVector.mean_const_mul,H.eigenvector_centered,mul_zero,Finset.sum_const_zero]

theorem synthesize_coordinate (H : HoldingFamily ι) (a : H.CenteredIndex → ℝ) (n : H.CenteredIndex) :
    H.coordinate (H.synthesize a) n=a n := by
  unfold synthesize coordinate
  rw [weightedInner_sum_right]
  simp_rw [weightedInner_const_mul_right,H.eigenvectors_orthonormal]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_eq_single n]
  · rw [ite_eq_left rfl]
  · intro k _ hkn
    rw [ite_eq_right (Ne.symm hkn)]
  · intro hn
    exact False.elim (hn (Finset.mem_univ n))

theorem synthesize_squareNorm (H : HoldingFamily ι) (a : H.CenteredIndex → ℝ) :
    H.sampling.squareNorm (H.synthesize a)=∑ n, (a n)^2 := by
  have hi := H.inner_coordinates (H.synthesize a) (H.synthesize a)
  rw [weightedInner_self,H.synthesize_centered,zero_mul,zero_add] at hi
  simpa only [H.synthesize_coordinate,pow_two] using hi

theorem eq_of_mean_coordinates (H : HoldingFamily ι) {f g : ι → ℝ}
    (hmean : H.sampling.mean f=H.sampling.mean g)
    (hcoord : ∀ n, H.coordinate f n=H.coordinate g n) : f=g := by
  calc
    f = (fun i ↦ H.sampling.mean f+∑ n, H.coordinate f n*H.eigenvector n i) := H.vector_expansion f
    _ = (fun i ↦ H.sampling.mean g+∑ n, H.coordinate g n*H.eigenvector n i) := by simp only [hmean,hcoord]
    _ = g := (H.vector_expansion g).symm

def inBand (H : HoldingFamily ι) (b : ℕ) (n : H.CenteredIndex) : Prop :=
  bandValue b≤H.eigenvalue n ∧ H.eigenvalue n<2*bandValue b

def bandProject (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) : ι → ℝ :=
  H.synthesize (fun n ↦ if H.inBand b n then H.coordinate f n else 0)

theorem bandProject_centered (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) :
    H.sampling.mean (H.bandProject b f)=0 := H.synthesize_centered _

theorem bandProject_coordinate (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (H.bandProject b f) n=if H.inBand b n then H.coordinate f n else 0 :=
  H.synthesize_coordinate _ n

theorem bandProject_squareNorm (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) :
    H.sampling.squareNorm (H.bandProject b f)=
      ∑ n, if H.inBand b n then (H.coordinate f n)^2 else 0 := by
  rw [bandProject,H.synthesize_squareNorm]
  apply Finset.sum_congr rfl
  intro n _
  split <;> simp only [zero_pow (by norm_num : 2≠0)]

theorem bandProject_idempotent (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) :
    H.bandProject b (H.bandProject b f)=H.bandProject b f := by
  apply H.eq_of_mean_coordinates
  · rw [H.bandProject_centered,H.bandProject_centered]
  · intro n
    by_cases hn : H.inBand b n
    · simp only [H.bandProject_coordinate,ite_eq_left hn]
    · simp only [H.bandProject_coordinate,ite_eq_right hn]

theorem bandProject_commutes_generator (H : HoldingFamily ι) (b : ℕ) (f : ι → ℝ) :
    H.bandProject b (H.generator f)=H.generator (H.bandProject b f) := by
  apply H.eq_of_mean_coordinates
  · rw [H.bandProject_centered,H.generator_sampling_mean]
  · intro n
    rw [H.bandProject_coordinate,H.generator_coordinate,H.generator_coordinate,H.bandProject_coordinate]
    split <;> ring

theorem bandProject_selfadjoint (H : HoldingFamily ι) (b : ℕ) (f g : ι → ℝ) :
    weightedInner H.sampling (H.bandProject b f) g=weightedInner H.sampling f (H.bandProject b g) := by
  rw [H.inner_coordinates,H.inner_coordinates,H.bandProject_centered,H.bandProject_centered,
    zero_mul,mul_zero,zero_add,zero_add]
  apply Finset.sum_congr rfl
  intro n _
  rw [H.bandProject_coordinate,H.bandProject_coordinate]
  split <;> ring

end
end Tournament.HoldingFamily

namespace Tournament.Upper

theorem bandValue_succ (b : ℕ) : bandValue (b+1)=2*bandValue b := by
  unfold bandValue
  rw [pow_succ]
  ring

theorem bandValue_mono {b c : ℕ} (hbc : b≤c) : bandValue b≤bandValue c := by
  have hp : (2:ℝ)^b≤2^c := pow_le_pow_right₀ (by norm_num) hbc
  unfold bandValue
  linarith

theorem exists_spectral_band (m : ℕ) {α : ℝ} (hα : 1/2≤α) (hαm : α<bandValue m) :
    ∃ b : Fin m, bandValue b.val≤α ∧ α<2*bandValue b.val := by
  induction m with
  | zero =>
    have hz : bandValue 0=1/2 := by norm_num [bandValue]
    rw [hz] at hαm
    linarith
  | succ m ih =>
    by_cases ham : α<bandValue m
    · obtain ⟨b,hb⟩ := ih ham
      exact ⟨b.castSucc,hb⟩
    · refine ⟨Fin.last m,le_of_not_gt ham,?_⟩
      rw [bandValue_succ] at hαm
      exact hαm

end Tournament.Upper

namespace Tournament.HoldingFamily

open Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem inBand_unique (H : HoldingFamily ι) {b c : ℕ} {n : H.CenteredIndex}
    (hb : H.inBand b n) (hc : H.inBand c n) : b=c := by
  rcases lt_trichotomy b c with hbc | hbc | hbc
  · have hm := bandValue_mono (show b+1≤c by omega)
    rw [bandValue_succ] at hm
    exact False.elim (not_lt_of_ge (le_trans hm hc.1) hb.2)
  · exact hbc
  · have hm := bandValue_mono (show c+1≤b by omega)
    rw [bandValue_succ] at hm
    exact False.elim (not_lt_of_ge (le_trans hm hb.1) hc.2)

end
end Tournament.HoldingFamily
