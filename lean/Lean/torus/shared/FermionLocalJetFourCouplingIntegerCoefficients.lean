import torus.shared.FermionLocalJetFourCouplingFirstRelative

/-! Exact integer-polynomial coefficients of the independently defined
S45 rotation. These formulas expose the true source coefficients to ordinary
finite arithmetic without replacing the rotation by certificate literals. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators

def integerS45Polynomial (z T : ℕ) : MvPolynomial (Fin 2) ℤ :=
  (MvPolynomial.X 0-MvPolynomial.X 1)^z *
    (MvPolynomial.X 0+MvPolynomial.X 1)^(T-z)

def integerS45Coefficient (z T p : ℕ) : ℤ :=
  (integerS45Polynomial z T).coeff (twoExponent p (T-p))

theorem integerS45Coefficient_cast (z T p : ℕ) :
    (integerS45Coefficient z T p : ℂ) =
      (((MvPolynomial.X 0-MvPolynomial.X 1)^z *
        (MvPolynomial.X 0+MvPolynomial.X 1)^(T-z) : Core (Fin 2) ℂ).coeff
          (twoExponent p (T-p))) := by
  have h := MvPolynomial.coeff_map (Int.castRingHom ℂ)
    (integerS45Polynomial z T) (twoExponent p (T-p))
  simpa only [integerS45Coefficient, integerS45Polynomial, map_mul, map_pow,
    map_sub, map_add, MvPolynomial.map_X, Int.coe_castRingHom] using h.symm

/-- Positive factorial roots are kept explicit; the sole signed quantity
is the integer coefficient of the original sum/difference polynomial. -/
theorem s45_integer_coefficient (z T p : ℕ) (hz : z≤T) (hp : p≤T) :
    s45 z T p = (integerS45Coefficient z T p : ℂ) *
      factorialRootNat p * factorialRootNat (T-p) /
      (factorialRootNat z * factorialRootNat (T-z) * (Real.sqrt (2:ℝ):ℂ)^T) := by
  let z' : Fin (T+1) := ⟨z,Nat.lt_succ_of_le hz⟩
  let p' : Fin (T+1) := ⟨p,Nat.lt_succ_of_le hp⟩
  have he := coefficient45_eq_coeff T z' p'
  rw [couplingPolynomial45_eq_paper] at he
  rw [← s45_in_range] at he
  change s45 z T p = _ at he
  simp only [z', p', smul_pow, smul_mul_smul_comm, smul_smul,
    MvPolynomial.coeff_smul, smul_eq_mul] at he
  rw [← pow_add, Nat.add_sub_of_le hz, inv_pow,
    ← integerS45Coefficient_cast z T p] at he
  rw [he]
  ring

/-- Product of the two original 45-degree coefficients. The intermediate
factorial root cancels, so every four-body coefficient has one fixed
r!(D-r)!(T-D)! denominator, independent of p,j,k. -/
theorem paperS45_integer_roots (r D T p j k : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hT : p+j+k=T) (hrjk : r≤j+k) :
    paperS45 r D T p j k =
      (integerS45Coefficient r (j+k) j : ℂ) *
      (integerS45Coefficient (D-r) (T-r) p : ℂ) *
      (Real.sqrt (2:ℝ):ℂ) * factorialRootNat p * factorialRootNat j * factorialRootNat k /
      (factorialRootNat r * factorialRootNat (D-r) * factorialRootNat (T-D) *
        (Real.sqrt (2:ℝ):ℂ)^(j+k+T-r)) := by
  have hp : p≤T-r := by omega
  have hz : D-r≤T-r := Nat.sub_le_sub_right hDT r
  have hq : T-r-p=j+k-r := by omega
  have hn : T-r-(D-r)=T-D := by omega
  have hj : j≤j+k := Nat.le_add_right j k
  have hs2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  rw [paperS45, if_pos ⟨hrD,hDT,hT⟩,
    s45_integer_coefficient r (j+k) j hrjk hj,
    s45_integer_coefficient (D-r) (T-r) p hz hp]
  rw [Nat.add_sub_cancel_left, hq, hn]
  have hex : j+k+T-r=(j+k)+(T-r) := by omega
  rw [hex,pow_add]
  field_simp [factorialRootNat_ne_zero,hs2] <;> ring

#print axioms integerS45Coefficient_cast
#print axioms s45_integer_coefficient
#print axioms paperS45_integer_roots
end TorusLean.Shared.FermionLocalJet.FourCoupling
