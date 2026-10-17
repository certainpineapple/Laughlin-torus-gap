import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge

/- Symmetry of the original full ordered source, used only to derive the
second half of literal matrix-entry obligations. No source pair is removed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate

theorem integerFourErrorMatrix_symmetric (D : ℕ)
    (i j : Fin ((D+1)/2)) :
    integerFourErrorMatrix D i j = integerFourErrorMatrix D j i := by
  let r := originalCopyMode D i
  let s := originalCopyMode D j
  have hn (u : OddMode D) : copyInverseRoot D u ≠ 0 := by
    unfold copyInverseRoot
    exact inv_ne_zero (mul_ne_zero (factorialRootNat_ne_zero _)
      (factorialRootNat_ne_zero _))
  have h := certificateFourMatrix_symmetric D r.val.val s.val.val
  rw [certificateFourMatrix_eq_integer_error D r s,
    certificateFourMatrix_eq_integer_error D s r] at h
  have hc : (integerFourError D r.val.val s.val.val : ℂ) =
      (integerFourError D s.val.val r.val.val : ℂ) := by
    apply mul_left_cancel₀ (mul_ne_zero (hn r) (hn s))
    calc
      _ = copyInverseRoot D s * copyInverseRoot D r *
          (integerFourError D s.val.val r.val.val : ℂ) := h
      _ = _ := by ring
  have hq := Rat.cast_injective (α := ℂ) hc
  simpa only [integerFourErrorMatrix,r,s,originalCopyMode] using hq

theorem originalErrorRational_symmetric (D : ℕ)
    (i j : Fin ((D+1)/2)) :
    OAI.Laughlin.Certificate.errorRational D i j =
      OAI.Laughlin.Certificate.errorRational D j i := by
  rw [← integerFourErrorMatrix_eq_originalY]
  exact integerFourErrorMatrix_symmetric D i j

#print axioms integerFourErrorMatrix_symmetric
#print axioms originalErrorRational_symmetric
end TorusLean.Shared.FermionLocalJet.FourCoupling
