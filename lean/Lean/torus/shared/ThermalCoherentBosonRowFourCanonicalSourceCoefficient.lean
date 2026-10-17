import torus.shared.ThermalCoherentBosonRowCanonicalAuxiliary
import torus.shared.BosonFiniteCertificateNatFourRows

/-! Exact scalar conversion of the original four-body normal tensor into
its decoded pair/spectator sources. The literal normal coefficient and its
annihilator orbital metric are retained, as are both ordered pair indices.
This file does not define a four-body operator from its proposed target. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

/-- The signed original integer, after its actual canonical orbital scaling. -/
theorem fourCanonical_alpha_scale (t p j : ℕ) (c : ℤ) :
    (alphaOf t p j c : ℂ)*natPairNormalization p =
      ((c:ℂ)/1000000000000)*(factorialRootNat (p+j-t)/factorialRootNat j) := by
  rw [← pairScale_cast]
  have h : alphaOf t p j c * pairScale p =
      ((c:ℝ)/1000000000000) *
        (Real.sqrt ((p+j-t).factorial:ℝ)/Real.sqrt (j.factorial:ℝ)) := by
    unfold alphaOf
    have hp := ne_of_gt (pairScale_pos p)
    have hj : Real.sqrt (j.factorial:ℝ)≠0 := by positivity
    field_simp [hp,hj]
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [factorialRootNat] using hc

private theorem root_factorial (n : ℕ) :
    (n.factorial:ℂ)=(factorialRootNat n)^2 := by
  unfold factorialRootNat
  exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg n.factorial)).symm

/-- All orbital factorials in one original term cancel to exactly the two
original decoded coefficients and the two ordered pair coefficients. -/
theorem fourCanonical_originalTerm_coefficient
    (t p j p' j' a b : ℕ) (c c' : ℤ) :
    ((natFourOriginalTerm t p j p' j' a b c c').coefficient:ℂ) /
        (natFourOrbitalMetric (natFourOriginalTerm t p j p' j' a b c c').annihilators:ℂ) *
      wordScale factorialRootNat (natFourOriginalTerm t p j p' j' a b c c').creators *
      wordScale factorialRootNat (natFourOriginalTerm t p j p' j' a b c c').annihilators =
        (alphaOf t p j c:ℂ)*(alphaOf t p' j' c':ℂ)*
          natPairNormalization p*natPairNormalization p'*
          pairCoefficientNat p a*pairCoefficientNat p' b := by
  have hright : (alphaOf t p j c:ℂ)*(alphaOf t p' j' c':ℂ)*
      natPairNormalization p*natPairNormalization p'*
      pairCoefficientNat p a*pairCoefficientNat p' b =
      ((alphaOf t p j c:ℂ)*natPairNormalization p)*
        ((alphaOf t p' j' c':ℂ)*natPairNormalization p')*
          pairCoefficientNat p a*pairCoefficientNat p' b := by ring
  rw [hright,fourCanonical_alpha_scale,fourCanonical_alpha_scale]
  simp only [natFourOriginalTerm,natFourOriginalCoefficient,natFourDecodedRowEntry,
    natFourOrbitalMetric,wordScale,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one,pairCoefficientNat]
  push_cast
  simp_rw [root_factorial]
  field_simp [factorialRootNat_ne_zero]
  <;> ring

/-- The literal pair word expansion, with both orders retained even when
indices repeat. Spectator labels remain arbitrary natural numbers. -/
theorem fourCanonical_pair_word (p j q : ℕ) :
    (pairCOMSeed p*MvPolynomial.X j)*MvPolynomial.X q =
      ∑ a ∈ Finset.range (p+1),
        (natPairNormalization p*pairCoefficientNat p a) •
          (wordPolynomial [a,p-a,j,q] : Core ℕ ℂ) := by
  rw [pairCOMSeed_eq_canonical_creator,canonicalPairCreatorNat_apply]
  simp only [Finset.smul_sum,Finset.sum_mul,smul_mul_assoc,mul_one,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [wordPolynomial,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    mul_one,mul_assoc]

#print axioms fourCanonical_alpha_scale
#print axioms fourCanonical_originalTerm_coefficient
#print axioms fourCanonical_pair_word
end TorusLean.Shared.ThermalCoherentBosonRows
