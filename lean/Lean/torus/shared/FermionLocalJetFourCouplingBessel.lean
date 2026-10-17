import torus.shared.FermionLocalJetFourCouplingColumns
import torus.shared.FermionLocalJetFourInputBudget
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Bessel on the original finite coefficient input, before physical substitution.
The index conversion retains each j<k exactly once and all odd relative copies.
No orthogonality of raw torus jets or physical wedge images is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

abbrev InputIndex (D : ℕ) := (p : Fin (D+1)) × Fin (D-p.val+1)
abbrev OddMode (D : ℕ) := {r : Fin (D+1) // Odd r.val}

def maskedS45 (D : ℕ) (r : OddMode D) (q : InputIndex D) : ℂ :=
  if q.2.val < D-q.1.val-q.2.val then highestS45 D r.val.val q.1.val q.2.val else 0

theorem maskedS45_star (D : ℕ) (r : OddMode D) (q : InputIndex D) :
    star (maskedS45 D r q) = maskedS45 D r q := by
  unfold maskedS45
  split_ifs <;> simp only [highestS45_star,star_zero]

theorem maskedS45_rows (D : ℕ) (r s : OddMode D) :
    (∑ q : InputIndex D, star (maskedS45 D r q) * maskedS45 D s q) =
      if r=s then 1 else 0 := by
  classical
  have h := highestS45_odd_rows D r.val.val s.val.val
    (Nat.le_of_lt_succ r.val.isLt) (Nat.le_of_lt_succ s.val.isLt) r.property s.property
  simp only [Fintype.sum_sigma,maskedS45]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  · simp only [Subtype.ext_iff,Fin.ext_iff]

/-- Scalar Bessel, proved from the actual two normalized rotations and the
antisymmetric spectator half-space. There is no supplied Gram hypothesis. -/
theorem highestS45_scalar_bessel (D : ℕ) (a : InputIndex D → ℂ) :
    (∑ r : OddMode D, ‖∑ q : InputIndex D, maskedS45 D r q * a q‖^2) ≤
      ∑ q : InputIndex D, ‖a q‖^2 := by
  classical
  let v : OddMode D → EuclideanSpace ℂ (InputIndex D) :=
    fun r => WithLp.toLp 2 (fun q => maskedS45 D r q)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro r s
    change (∑ q : InputIndex D, maskedS45 D s q * star (maskedS45 D r q)) = _
    simpa only [mul_comm] using maskedS45_rows D r s
  have hi (r : OddMode D) : inner ℂ (v r) (WithLp.toLp 2 a) =
      ∑ q : InputIndex D, maskedS45 D r q * a q := by
    change (∑ q : InputIndex D, a q * star (maskedS45 D r q)) = _
    simp only [maskedS45_star,mul_comm]
  have h := hv.sum_inner_products_le (WithLp.toLp 2 a) (s := Finset.univ)
  rw [EuclideanSpace.norm_sq_eq] at h
  simpa only [hi] using h

/-- Exact conversion from triangular (p,j,k) indices to the original unordered
(j,k) inputs used in the independently proved 1222 same-H budget. -/
theorem fourInput_triangle_reindex (D : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ q : InputIndex D, if q.2.val < D-q.1.val-q.2.val then
      f q.1.val q.2.val (D-q.1.val-q.2.val) else 0) =
    ∑ jk ∈ fourInputPairs D, f (D-jk.1.val-jk.2.val) jk.1.val jk.2.val := by
  classical
  rw [← Finset.sum_filter]
  let index : InputIndex D → Fin (D+1) × Fin (D+1) := fun q =>
    (⟨q.2.val,by have := q.1.isLt; have := q.2.isLt; omega⟩,
     ⟨D-q.1.val-q.2.val,by omega⟩)
  apply Finset.sum_bij (fun q _ => index q)
  · intro q hq
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hq
    simp only [fourInputPairs,Finset.mem_filter,Finset.mem_univ,true_and,index]
    have := q.1.isLt
    have := q.2.isLt
    omega
  · intro q hq v hv he
    have hj := congrArg (fun jk : Fin (D+1) × Fin (D+1) => jk.1.val) he
    have hk := congrArg (fun jk : Fin (D+1) × Fin (D+1) => jk.2.val) he
    dsimp only [index] at hj hk
    have hpq := q.1.isLt
    have hjq := q.2.isLt
    have hpv := v.1.isLt
    have hjv := v.2.isLt
    have hp : q.1=v.1 := Fin.ext (by omega)
    cases q with | mk p j =>
      cases v with | mk p' j' =>
        dsimp only at hp hj
        subst p'
        congr 1
        exact Fin.ext hj
  · intro jk hjk
    simp only [fourInputPairs,Finset.mem_filter,Finset.mem_univ,true_and] at hjk
    let q : InputIndex D := ⟨⟨D-jk.1.val-jk.2.val,by omega⟩,
      ⟨jk.1.val,by dsimp only; omega⟩⟩
    have hk : D-q.1.val-q.2.val=jk.2.val := by dsimp only [q]; omega
    refine ⟨q,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,hk]
      exact hjk.1
    · apply Prod.ext
      · rfl
      · exact Fin.ext hk
  · intro q hq
    dsimp only [index]
    have hp : D-q.2.val-(D-q.1.val-q.2.val)=q.1.val := by
      have := q.1.isLt
      have := q.2.isLt
      omega
    rw [hp]

#print axioms maskedS45_star
#print axioms maskedS45_rows
#print axioms highestS45_scalar_bessel
#print axioms fourInput_triangle_reindex
end TorusLean.Shared.FermionLocalJet.FourCoupling
