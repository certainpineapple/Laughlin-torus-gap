import torus.shared.BosonFiniteCertificateNatCOMLower
import torus.shared.BosonFiniteCertificateCOMWord

/-! The actual Nat lowering restricts to the already checked Fin9 lowering,
without a boundary guard: lowering never creates a larger orbital label.
This is an operator identity on all finite-variable polynomials, not just a
comparison of matrices or an abstract identification of their kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem canonicalCOMLower9_C (c : ℂ) : canonicalCOMLower9 (MvPolynomial.C c) = 0 := by
  have hOne : canonicalCOMLower9 1 = 0 := by
    simpa only [mul_one,one_mul,add_eq_left] using (canonicalCOMLower9_mul 1 1).symm
  rw [MvPolynomial.C_eq_smul_one,map_smul,hOne,smul_zero]

theorem canonicalCOMLowerNat_rename_X (j : Fin 9) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val (MvPolynomial.X j)) =
      MvPolynomial.rename Fin.val (canonicalCOMLower9 (MvPolynomial.X j)) := by
  rw [MvPolynomial.rename_X,canonicalCOMLowerNat_X]
  by_cases h0 : j.val=0
  · have hj : j=0 := Fin.ext h0
    rw [hj,canonicalCOMLower9_X_zero,map_zero]
    simp
  · let a : Fin 8 := ⟨j.val-1,by have := j.isLt; omega⟩
    have ha : raiseTarget9 a = j := by
      apply Fin.ext
      dsimp [raiseTarget9,a]
      omega
    have hv : a.val+1=j.val := by dsimp [a]; omega
    have hx := canonicalCOMLower9_X_target a
    rw [ha] at hx
    rw [hx,map_smul,MvPolynomial.rename_X]
    have hcast : (a.val : ℝ)+1=(j.val : ℝ) := by exact_mod_cast hv
    rw [hcast]
    rfl

/-- True all-core finite-to-Nat lowering intertwining. -/
theorem canonicalCOMLowerNat_rename (p : Core (Fin 9) ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val p) =
      MvPolynomial.rename Fin.val (canonicalCOMLower9 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.rename_C,canonicalCOMLowerNat_C,canonicalCOMLower9_C,map_zero]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [map_mul,canonicalCOMLowerNat_mul,hp,canonicalCOMLowerNat_rename_X,
      canonicalCOMLower9_mul,map_add,map_mul,map_mul]

theorem canonicalCOMLowerNat_rename_eq_zero_iff (p : Core (Fin 9) ℂ) :
    canonicalCOMLowerNat (MvPolynomial.rename Fin.val p) = 0 ↔ canonicalCOMLower9 p = 0 := by
  rw [canonicalCOMLowerNat_rename]
  exact MvPolynomial.rename_eq_zero_iff_of_injective _ Fin.val_injective

theorem nat_weight_mapDomain_fin9 (n : Fin 9 →₀ ℕ) :
    Finsupp.weight id (n.mapDomain Fin.val) = Finsupp.weight Fin.val n := by
  simp only [Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem rename_canonicalBlock_bihomogeneous {B : Type*} [Fintype B] [DecidableEq B]
    (d : ℕ) (occ : B → (Fin 9 →₀ ℕ))
    (hN : ∀ b, (occ b).degree=3)
    (hd : ∀ b, Finsupp.weight Fin.val (occ b)=d) (x : B → ℂ) :
    (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) occ x)).IsHomogeneous 3 ∧
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) occ x)).IsWeightedHomogeneous id d := by
  constructor
  · exact (canonicalBlock_bihomogeneous d occ hN hd x).1.rename_isHomogeneous
  · change MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) occ x) ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ id d
    unfold canonicalBlock canonicalMonomial
    rw [map_sum]
    apply Submodule.sum_mem
    intro b _
    rw [map_smul,MvPolynomial.rename_monomial]
    apply Submodule.smul_mem
    exact MvPolynomial.isWeightedHomogeneous_monomial id _ _
      ((nat_weight_mapDomain_fin9 (occ b)).trans (hd b))

#print axioms canonicalCOMLowerNat_rename
#print axioms canonicalCOMLowerNat_rename_eq_zero_iff
#print axioms rename_canonicalBlock_bihomogeneous
end TorusLean.BosonFiniteCertificate
