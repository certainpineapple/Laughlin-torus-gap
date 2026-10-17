import torus.shared.FermionLocalJetFourCouplingRotation

/-! Real coefficients and the exact spectator exchange parity of the
manuscript's two-mode coefficient. Odd relative rows are antisymmetric;
their diagonal input vanishes before any physical CAR substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open TorusLean.Boson.SpectatorControl
open scoped BigOperators ComplexConjugate

def twoExponent (p q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p + Finsupp.single 1 q

private theorem factorialRoot_star (p : ℕ) : star (factorialRootNat p) = factorialRootNat p := by
  simp [factorialRootNat,Complex.star_def]

private theorem factorialRoot_sq (p : ℕ) : (factorialRootNat p)^2 = (p.factorial : ℂ) := by
  unfold factorialRootNat
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p.factorial)

private theorem canonicalWord_monomial (T : ℕ) (p : Fin (T+1)) :
    canonicalWord T p = MvPolynomial.monomial (twoExponent p.val (T-p.val))
      (factorialRootNat p.val * factorialRootNat (T-p.val))⁻¹ := by
  simp [canonicalWord,normalizedSpectatorWord,twoExponent,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial,MvPolynomial.smul_monomial]

theorem canonicalWord_inner_coeff (T : ℕ) (p : Fin (T+1)) (f : Core (Fin 2) ℂ) :
    ip (canonicalWord T p) f = factorialRootNat p.val * factorialRootNat (T-p.val) *
      f.coeff (twoExponent p.val (T-p.val)) := by
  rw [canonicalWord_monomial,ip,occupationInner_monomial_left]
  have hw : occupationMetricWeight (fun _ : Fin 2 => 1) (twoExponent p.val (T-p.val)) =
      p.val.factorial * (T-p.val).factorial := by
    simp [occupationMetricWeight,twoExponent,Fin.prod_univ_two]
  rw [hw,Nat.cast_mul,← factorialRoot_sq,← factorialRoot_sq]
  simp only [star_inv₀,star_mul,factorialRoot_star]
  field_simp [factorialRootNat_ne_zero] <;> ring

theorem coefficient45_eq_coeff (T : ℕ) (z p : Fin (T+1)) :
    coefficient45 T z p = factorialRootNat p.val * factorialRootNat (T-p.val) *
      (couplingPolynomial45 T z).coeff (twoExponent p.val (T-p.val)) :=
  canonicalWord_inner_coeff T p _

theorem couplingPolynomial45_conjugate (T : ℕ) (z : Fin (T+1)) :
    MvPolynomial.map (starRingEnd ℂ) (couplingPolynomial45 T z) = couplingPolynomial45 T z := by
  rw [couplingPolynomial45_eq_paper]
  simp [MvPolynomial.smul_eq_C_mul,factorialRootNat,Complex.star_def]

theorem coefficient45_star (T : ℕ) (z p : Fin (T+1)) :
    star (coefficient45 T z p) = coefficient45 T z p := by
  have hc := congrArg (fun f : Core (Fin 2) ℂ => f.coeff (twoExponent p.val (T-p.val)))
    (couplingPolynomial45_conjugate T z)
  simp only [MvPolynomial.coeff_map] at hc
  change star ((couplingPolynomial45 T z).coeff (twoExponent p.val (T-p.val))) = _ at hc
  rw [coefficient45_eq_coeff]
  simp only [star_mul,factorialRoot_star,hc]
  ring

theorem s45_star (z T p : ℕ) : star (s45 z T p) = s45 z T p := by
  unfold s45
  split_ifs <;> simp only [coefficient45_star,star_zero]

private def flip : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
private def flipPoly : Core (Fin 2) ℂ →ₐ[ℂ] Core (Fin 2) ℂ := MvPolynomial.rename flip

private theorem flip_twoExponent (p q : ℕ) :
    Finsupp.mapDomain flip (twoExponent p q) = twoExponent q p := by
  simp [twoExponent,Finsupp.mapDomain_add,Finsupp.mapDomain_single,flip,add_comm]

private theorem coeff_flipPoly (f : Core (Fin 2) ℂ) (p q : ℕ) :
    (flipPoly f).coeff (twoExponent p q) = f.coeff (twoExponent q p) := by
  rw [← flip_twoExponent q p]
  exact MvPolynomial.coeff_rename_mapDomain flip flip.injective f _

theorem couplingPolynomial45_flip (T : ℕ) (z : Fin (T+1)) :
    flipPoly (couplingPolynomial45 T z) = (-1 : ℂ)^z.val • couplingPolynomial45 T z := by
  simp only [couplingPolynomial45_eq_paper,map_smul,map_mul,map_pow]
  have hs : flipPoly (MvPolynomial.X 0+MvPolynomial.X 1) =
      (MvPolynomial.X 0+MvPolynomial.X 1 : Core (Fin 2) ℂ) := by simp [flipPoly,flip,add_comm]
  have hd : flipPoly (MvPolynomial.X 0-MvPolynomial.X 1) =
      (-1 : ℂ) • (MvPolynomial.X 0-MvPolynomial.X 1 : Core (Fin 2) ℂ) := by
    simp [flipPoly,flip]
  rw [hs,hd,smul_comm ((Real.sqrt (2:ℝ):ℂ)⁻¹) (-1),smul_pow]
  simp only [smul_mul_assoc,smul_smul]
  rw [mul_comm]

theorem coefficient45_reflection (T : ℕ) (z p : Fin (T+1)) :
    coefficient45 T z ⟨T-p.val,by omega⟩ = (-1 : ℂ)^z.val * coefficient45 T z p := by
  have hc := congrArg (fun f : Core (Fin 2) ℂ => f.coeff (twoExponent p.val (T-p.val)))
    (couplingPolynomial45_flip T z)
  rw [coeff_flipPoly,MvPolynomial.coeff_smul] at hc
  simp only [smul_eq_mul] at hc
  have hp : p.val ≤ T := Nat.le_of_lt_succ p.isLt
  simp only [coefficient45_eq_coeff,Nat.sub_sub_self hp]
  rw [hc]
  ring

theorem s45_reflection (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    s45 z T (T-p) = (-1 : ℂ)^z * s45 z T p := by
  let z' : Fin (T+1) := ⟨z,Nat.lt_succ_of_le hz⟩
  let p' : Fin (T+1) := ⟨p,Nat.lt_succ_of_le hp⟩
  have h := coefficient45_reflection T z' p'
  simpa only [← s45_in_range,z',p'] using h

theorem s45_diagonal_odd_zero (z j : ℕ) (hz : z ≤ 2*j) (hodd : Odd z) :
    s45 z (2*j) j = 0 := by
  have h := s45_reflection z (2*j) j hz (by omega)
  have hp : (-1 : ℂ)^z = -1 := hodd.neg_one_pow
  rw [show 2*j-j=j by omega,hp] at h
  linear_combination (1/2 : ℂ)*h

#print axioms canonicalWord_inner_coeff
#print axioms coefficient45_eq_coeff
#print axioms couplingPolynomial45_conjugate
#print axioms coefficient45_star
#print axioms s45_star
#print axioms couplingPolynomial45_flip
#print axioms coefficient45_reflection
#print axioms s45_reflection
#print axioms s45_diagonal_odd_zero
end TorusLean.Shared.FermionLocalJet.FourCoupling
