module

public import Tournament.Probability.Correlations
public import Tournament.Foundations.WeightedInner
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem state_pair_mean_ordered (P : FiniteKernel ι) (p : ProbabilityVector ι) (hstat : P.Stationary p)
    (n t u : ℕ) (htu : t ≤ u) (hun : u ≤ n) (f g : ι → ℝ) :
    (law P p n).mean (fun hist ↦ f (stateAt n hist t)*g (stateAt n hist u))=
      FiniteKernel.weightedInner p f (((P.act)^[u-t]) g) := by
  by_cases heq : t=u
  · subst u
    simpa only [Nat.sub_self,Function.iterate_zero,Function.id_def,FiniteKernel.weightedInner] using
      stationary_stateAt_mean P p hstat n t hun (fun i ↦ f i*g i)
  · have hlt : t<u := lt_of_le_of_ne htu heq
    have hc := transition_future_mean P p hstat (fun i _ ↦ f i) n t u hlt hun g
    change (law P p n).mean (fun hist ↦ f (stateAt n hist t)*g (stateAt n hist u))=
      P.edgeSum p (fun i j ↦ f i*((P.act)^[u-t-1]) g j) at hc
    rw [P.edgeSum_cross p f (((P.act)^[u-t-1]) g)] at hc
    have hd : u-t=(u-t-1)+1 := by omega
    rw [hd,Function.iterate_succ_apply']
    exact hc

theorem reversible_state_pair_mean (P : FiniteKernel ι) (p : ProbabilityVector ι) (hr : P.Reversible p)
    (n t u : ℕ) (htn : t ≤ n) (hun : u ≤ n) (f g : ι → ℝ) :
    (law P p n).mean (fun hist ↦ f (stateAt n hist t)*g (stateAt n hist u))=
      FiniteKernel.weightedInner p f (((P.act)^[Nat.dist t u]) g) := by
  rcases le_total t u with htu | hut
  · rw [Nat.dist_eq_sub_of_le htu]
    exact state_pair_mean_ordered P p (P.reversible_stationary p hr) n t u htu hun f g
  · have hfun : (fun hist : History ι n ↦ f (stateAt n hist t)*g (stateAt n hist u))=
        (fun hist ↦ g (stateAt n hist u)*f (stateAt n hist t)) := funext (fun _ ↦ mul_comm _ _)
    rw [hfun,state_pair_mean_ordered P p (P.reversible_stationary p hr) n u t hut htn g f,
      Nat.dist_eq_sub_of_le_right hut]
    rw [FiniteKernel.weightedInner_iterate_selfadjoint P p hr,FiniteKernel.weightedInner_comm]

theorem state_sum_square_mean (P : FiniteKernel ι) (p : ProbabilityVector ι) (hr : P.Reversible p)
    (n : ℕ) (f : ℕ → ι → ℝ) :
    (law P p n).mean (fun hist ↦ (∑ t ∈ Finset.range (n+1), f t (stateAt n hist t))^2)=
      ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        FiniteKernel.weightedInner p (f t) (((P.act)^[Nat.dist t u]) (f u)) := by
  have hfun : (fun hist : History ι n ↦ (∑ t ∈ Finset.range (n+1), f t (stateAt n hist t))^2)=
      (fun hist ↦ ∑ t ∈ Finset.range (n+1), ∑ u ∈ Finset.range (n+1),
        f t (stateAt n hist t)*f u (stateAt n hist u)) := by
    funext hist
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    exact Finset.mul_sum _ _ _
  rw [hfun,ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact reversible_state_pair_mean P p hr n t u
    (by have := Finset.mem_range.mp ht; omega) (by have := Finset.mem_range.mp hu; omega) (f t) (f u)

end
end Tournament.FinitePath
