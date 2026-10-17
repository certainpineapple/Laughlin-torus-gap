import torus.shared.ThermalCoherentJacobiFourParseval

/-! The manuscript's normalized two-mode 45-degree coefficient, obtained
from the actual second quantization of the existing orbital unitary.
Only the formal coefficient input space is used here, never the boson W4 image.
The relative mode is the second input of the frozen sum/difference rotation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.TwoBodyLift
open TorusLean.BosonFiniteCertificate TorusLean.Boson.SpectatorControl
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

def canonicalWord (T : ℕ) (p : Fin (T+1)) : Core (Fin 2) ℂ :=
  normalizedSpectatorWord p.val (T-p.val)

private theorem canonicalWord_eq_frame (T : ℕ) (p : Fin (T+1)) :
    canonicalWord T p = degreeFrame T ((degreeIndexEquiv T).symm p) := by
  symm
  simpa [canonicalWord,degreeIndexEquiv] using
    degreeFrame_eq_spectatorWord T ((degreeIndexEquiv T).symm p)

theorem canonicalWord_homogeneous (T : ℕ) (p : Fin (T+1)) :
    (canonicalWord T p).IsHomogeneous T := by
  rw [canonicalWord_eq_frame]
  exact degreeFrame_homogeneous T _

theorem canonicalWord_orthonormal (T : ℕ) (p q : Fin (T+1)) :
    ip (canonicalWord T p) (canonicalWord T q) = if p=q then 1 else 0 := by
  rw [canonicalWord_eq_frame,canonicalWord_eq_frame,degreeFrame_orthonormal]
  simp only [(degreeIndexEquiv T).symm.injective.eq_iff]

theorem canonicalWord_expansion (T : ℕ) (f : Core (Fin 2) ℂ) (hf : f.IsHomogeneous T) :
    f = ∑ p : Fin (T+1), ip (canonicalWord T p) f • canonicalWord T p := by
  calc
    _ = ∑ n : DegreeIndex T, ip (degreeFrame T n) f • degreeFrame T n :=
      degreeFrame_expansion T f hf
    _ = _ := by
      simpa only [canonicalWord_eq_frame] using
        (Equiv.sum_comp (degreeIndexEquiv T).symm
          (fun n : DegreeIndex T => ip (degreeFrame T n) f • degreeFrame T n)).symm

private def reverseIndex (T : ℕ) (z : Fin (T+1)) : Fin (T+1) :=
  ⟨T-z.val,by omega⟩

private theorem reverseIndex_injective (T : ℕ) : Function.Injective (reverseIndex T) := by
  intro z w h
  have hv := congrArg Fin.val h
  simp only [reverseIndex] at hv
  apply Fin.ext
  have hz := z.isLt
  have hw := w.isLt
  omega

/-- Relative z and COM T-z. The existing rotation sends X0 to sum and X1
to difference, so the actual input word has degrees (T-z,z). -/
def couplingPolynomial45 (T : ℕ) (z : Fin (T+1)) : Core (Fin 2) ℂ :=
  rotateSpectatorPolynomial (canonicalWord T (reverseIndex T z))

def coefficient45 (T : ℕ) (z p : Fin (T+1)) : ℂ :=
  ip (canonicalWord T p) (couplingPolynomial45 T z)

theorem couplingPolynomial45_homogeneous (T : ℕ) (z : Fin (T+1)) :
    (couplingPolynomial45 T z).IsHomogeneous T :=
  rotateSpectatorPolynomial_homogeneous T _ (canonicalWord_homogeneous T _)

theorem coefficient45_expansion (T : ℕ) (z : Fin (T+1)) :
    couplingPolynomial45 T z = ∑ p : Fin (T+1), coefficient45 T z p • canonicalWord T p :=
  canonicalWord_expansion T _ (couplingPolynomial45_homogeneous T z)

/-- Full row orthogonality, proved through actual Gamma(U) and the complete
finite factorial degree sector, not supplied as a coefficient assumption. -/
theorem coefficient45_rows_orthonormal (T : ℕ) (z w : Fin (T+1)) :
    (∑ p : Fin (T+1), star (coefficient45 T z p) * coefficient45 T w p) =
      if z=w then 1 else 0 := by
  have he := canonicalWord_expansion T (couplingPolynomial45 T z)
    (couplingPolynomial45_homogeneous T z)
  calc
    _ = ip (couplingPolynomial45 T z) (couplingPolynomial45 T w) := by
      conv_rhs => rw [he,inner_sum_left]
      simp only [TwoBodyLift.inner_smul_left,coefficient45]
    _ = ip (canonicalWord T (reverseIndex T z)) (canonicalWord T (reverseIndex T w)) :=
      rotateSpectatorPolynomial_inner _ _
    _ = _ := by
      rw [canonicalWord_orthonormal]
      simp only [(reverseIndex_injective T).eq_iff]

/-- Literal normalized polynomial of eq:F-coupling for u=v=1/sqrt(2).
The sqrt-factorial product is the positive square root of z!(T-z)!. -/
theorem couplingPolynomial45_eq_paper (T : ℕ) (z : Fin (T+1)) :
    couplingPolynomial45 T z =
      (factorialRootNat z.val * factorialRootNat (T-z.val))⁻¹ •
        ((((Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0-MvPolynomial.X 1))^z.val) *
          (((Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0+MvPolynomial.X 1))^(T-z.val))) := by
  have hz : z.val ≤ T := Nat.le_of_lt_succ z.isLt
  simp only [couplingPolynomial45,canonicalWord,reverseIndex,
    Nat.sub_sub_self hz,normalizedSpectatorWord,map_smul,map_mul,map_pow,
    rotateSpectatorPolynomial_X_zero,rotateSpectatorPolynomial_X_one]
  simp only [mul_comm]

/-- Natural-index version with the manuscript's explicit zero extension. -/
def s45 (z T p : ℕ) : ℂ :=
  if hz : z ≤ T then
    if hp : p ≤ T then coefficient45 T ⟨z,Nat.lt_succ_of_le hz⟩ ⟨p,Nat.lt_succ_of_le hp⟩
    else 0
  else 0

theorem s45_in_range (T : ℕ) (z p : Fin (T+1)) :
    s45 z.val T p.val = coefficient45 T z p := by
  simp only [s45,dif_pos (Nat.le_of_lt_succ z.isLt),dif_pos (Nat.le_of_lt_succ p.isLt)]

theorem s45_outside (z T p : ℕ) (h : T < z ∨ T < p) : s45 z T p = 0 := by
  rcases h with hz | hp
  · simp only [s45,dif_neg (Nat.not_le.mpr hz)]
  · by_cases hz : z ≤ T <;> simp [s45,hz,Nat.not_le.mpr hp]

/-- Exact defining polynomial identity for the original 45-degree s coefficient. -/
theorem s45_polynomial_identity (z T : ℕ) (hz : z ≤ T) :
    (factorialRootNat z * factorialRootNat (T-z))⁻¹ •
      ((((Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0-MvPolynomial.X 1))^z) *
        (((Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0+MvPolynomial.X 1))^(T-z))) =
      ∑ p : Fin (T+1), s45 z T p.val • canonicalWord T p := by
  let z' : Fin (T+1) := ⟨z,Nat.lt_succ_of_le hz⟩
  have he := coefficient45_expansion T z'
  rw [couplingPolynomial45_eq_paper] at he
  simpa only [← s45_in_range,z'] using he

#print axioms canonicalWord_homogeneous
#print axioms canonicalWord_orthonormal
#print axioms canonicalWord_expansion
#print axioms couplingPolynomial45_homogeneous
#print axioms coefficient45_expansion
#print axioms coefficient45_rows_orthonormal
#print axioms couplingPolynomial45_eq_paper
#print axioms s45_in_range
#print axioms s45_outside
#print axioms s45_polynomial_identity
end TorusLean.Shared.FermionLocalJet.FourCoupling
