import torus.shared.BosonFiniteCertificateCanonicalTransport
import torus.shared.BosonFiniteCertificateCanonicalGram
import torus.shared.BosonFiniteCertificateConjugationPair
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonFiniteCertificateConjugation

/-- Full finite-occupation block, before taking relative coordinates. -/
def canonicalPairHamiltonianForm {n : ℕ} (d : ℕ) (occ : Fin n → (Fin 9 →₀ ℕ)) :
    Matrix (Fin n) (Fin n) ℂ := fun a b =>
  ((List.range (d+1)).map fun p =>
    ((p.factorial : ℂ) / (2 : ℂ)^(p+1)) *
      ip (canonicalPair9 p (canonicalMonomial (factorialScale 8) (occ a)))
        (canonicalPair9 p (canonicalMonomial (factorialScale 8) (occ b)))).sum

theorem canonicalMonomialFamily_gram {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (hocc : Function.Injective occ) (hdegree : ∀ a, (occ a).degree = 3) :
    familyGram (fun a => canonicalThreeMonomial (factorialScale 8) (occ a) (hdegree a)) =
      Matrix.diagonal (fun a => (occupationMetricWeight (factorialScale 8) (occ a) : ℂ)) := by
  ext a b
  change ip (canonicalMonomial (factorialScale 8) (occ a))
    (canonicalMonomial (factorialScale 8) (occ b)) = _
  rw [canonicalMonomial_inner]
  by_cases h : a=b
  · subst b
    simp
  · have ho : occ a ≠ occ b := fun he => h (hocc he)
    simp [h, ho, Matrix.diagonal]

theorem rankOneRealization_apply_synthesis {r : ℕ}
    (w : Fin r → ThreeSector (Fin 9)) (C : Matrix (Fin r) (Fin r) ℂ)
    (f : ThreeSector (Fin 9)) :
    rankOneRealization w C f = familySynthesis w (C *ᵥ familyAnalysis w f) := by
  simp only [rankOneRealization, LinearMap.sum_apply, LinearMap.smul_apply,
    familyRank, LinearMap.coe_mk, AddHom.coe_mk, familySynthesis,
    familyAnalysis, Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]

theorem inverseGramRealization_synthesis_action {r : ℕ}
    (w : Fin r → ThreeSector (Fin 9)) (F J E : Matrix (Fin r) (Fin r) ℂ)
    (hF : familyGram w = F) (hJF : J*F=1) (y : Fin r → ℂ) :
    rankOneRealization w (inverseGramCoefficient J E) (familySynthesis w y) =
      familySynthesis w ((J*E) *ᵥ y) := by
  rw [rankOneRealization_apply_synthesis, familyAnalysis_synthesis, hF,
    Matrix.mulVec_mulVec]
  simp only [inverseGramCoefficient, Matrix.mul_assoc, hJF, Matrix.mul_one]

theorem inverseGramRealization_square_form {r : ℕ}
    (w : Fin r → ThreeSector (Fin 9)) (F J E : Matrix (Fin r) (Fin r) ℂ)
    (hF : familyGram w = F) (hFJ : F*J=1) (hJF : J*F=1) (x y : Fin r → ℂ) :
    ip (familySynthesis w x).val
      (rankOneRealization w (inverseGramCoefficient J E)
        (rankOneRealization w (inverseGramCoefficient J E) (familySynthesis w y))).val =
      star x ⬝ᵥ ((E*J*E) *ᵥ y) := by
  rw [inverseGramRealization_synthesis_action w F J E hF hJF y]
  rw [inverseGramRealization_form w F J E hF hFJ hJF x ((J*E) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms canonicalMonomialFamily_gram
#print axioms inverseGramRealization_synthesis_action
#print axioms inverseGramRealization_square_form
end TorusLean.BosonFiniteCertificate
