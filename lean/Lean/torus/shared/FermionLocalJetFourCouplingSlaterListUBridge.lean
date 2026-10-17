import torus.shared.FermionLocalJetFourCouplingSlaterListCoefficient
import OAI.Analysis.Laughlin.Operators.Certificate

/-! The executable convolution is exactly the manuscript U(1,z,T,p),
including its filter bounds. This is a reindexing theorem, not a table check. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
namespace SlaterListCandidate

theorem list_range_sum (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum=∑ h ∈ Finset.range n, f h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,Finset.sum_range_succ,ih]
    simp

theorem list_filter_sum (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℤ) :
    ((l.filter (fun h => decide (P h))).map f).sum=
      (l.map (fun h => if P h then f h else 0)).sum := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    by_cases hp : P h
    · simp [hp,ih]
    · simp [hp,ih]

theorem coefficientList_eq_U (z T p : ℕ) (hz : z≤T) (hp : p≤T) :
    coefficientList z T p=OAI.Laughlin.Certificate.U 1 z T p := by
  rw [coefficientList_sum,OAI.Laughlin.Certificate.U,if_pos ⟨hz,hp⟩,
    list_filter_sum,list_range_sum]
  simp only [Nat.cast_one,one_pow,mul_one]
  let f : ℕ → ℤ := fun h =>
    (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ)
  change (∑ h ∈ Finset.range (z+1), if h≤p ∧ p-h≤T-z then f h else 0)=
    ∑ h ∈ Finset.range (min p z+1), if p+z≤T+h then f h else 0
  symm
  calc
    _ = ∑ h ∈ Finset.range (min p z+1), if h≤p ∧ p-h≤T-z then f h else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      have hh' : h≤min p z := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
      have he : (p+z≤T+h) ↔ (h≤p ∧ p-h≤T-z) := by omega
      simp only [he]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro h hh hnot
      have hh' : h≤z := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
      have hout : ¬h<min p z+1 := by simpa only [Finset.mem_range] using hnot
      have hgt : ¬h≤p := by omega
      simp only [hgt,false_and,if_false]

theorem integerS45Coefficient_eq_U (z T p : ℕ) (hz : z≤T) (hp : p≤T) :
    integerS45Coefficient z T p=OAI.Laughlin.Certificate.U 1 z T p := by
  rw [integerS45Coefficient_eq_list z T p hz hp,coefficientList_eq_U z T p hz hp]

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.list_range_sum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.list_filter_sum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.coefficientList_eq_U
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.integerS45Coefficient_eq_U
