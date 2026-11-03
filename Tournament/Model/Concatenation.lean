module

public import Tournament.Model.Regret
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Tournament.Model

open scoped BigOperators

variable {ι : Type*}

def appendActions (h : ℕ) (X Y : ℕ → ι) (t : ℕ) : ι := if t<h then X t else Y (t-h)

theorem switchCount_append_prefix [DecidableEq ι] (n : ℕ) (X Y : ℕ → ι) :
    switchCount (n+1) (appendActions (n+1) X Y) = switchCount (n+1) X := by
  unfold switchCount
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t<n := by simpa only [Nat.add_sub_cancel] using Finset.mem_range.mp ht
  simp only [appendActions, ite_eq_left (by omega : t+1<n+1), ite_eq_left (by omega : t<n+1)]

theorem switchCount_append [DecidableEq ι] (n m : ℕ) (X Y : ℕ → ι) :
    switchCount ((n+1)+(m+1)) (appendActions (n+1) X Y) =
      switchCount (n+1) X + (if Y 0=X n then 0 else 1) + switchCount (m+1) Y := by
  let Z := appendActions (n+1) X Y
  have hlen : ((n+1)+(m+1))-1=n+(m+1) := by omega
  change (∑ t ∈ Finset.range (((n+1)+(m+1))-1), if Z (t+1)=Z t then 0 else 1) = _
  rw [hlen,Finset.sum_range_add]
  have hhead : (∑ t ∈ Finset.range n, if Z (t+1)=Z t then 0 else 1) = switchCount (n+1) X := by
    change _ = ∑ t ∈ Finset.range n, if X (t+1)=X t then 0 else 1
    apply Finset.sum_congr rfl
    intro t ht
    have htn := Finset.mem_range.mp ht
    simp only [Z,appendActions,ite_eq_left (by omega : t+1<n+1),ite_eq_left (by omega : t<n+1)]
  have hboundary : (if Z (n+0+1)=Z (n+0) then 0 else 1) = (if Y 0=X n then 0 else 1) := by
    simp [Z,appendActions]
  have htail : (∑ t ∈ Finset.range m, if Z (n+(t+1)+1)=Z (n+(t+1)) then 0 else 1) =
      switchCount (m+1) Y := by
    change _ = ∑ t ∈ Finset.range m, if Y (t+1)=Y t then 0 else 1
    apply Finset.sum_congr rfl
    intro t _
    have hnext : n+(t+1)+1-(n+1)=t+1 := by omega
    have hcurrent : n+(t+1)-(n+1)=t := by omega
    simp only [Z,appendActions,ite_eq_right (by omega : ¬n+(t+1)+1<n+1),
      ite_eq_right (by omega : ¬n+(t+1)<n+1),hnext,hcurrent]
  rw [hhead,Finset.sum_range_succ',htail,hboundary]
  omega

end Tournament.Model
