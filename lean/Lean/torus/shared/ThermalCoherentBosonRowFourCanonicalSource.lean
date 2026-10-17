import torus.shared.ThermalCoherentBosonRowFourCanonicalSourceRows
import torus.shared.BosonFiniteCertificateNatFourRankSource

/-! Source identity for the original four-body canonical operator. The
operator on the left is the independently defined original normal-word
operator; the right uses the unique decoded Y_i sources. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators

/-- The original K4 tensor, with its literal coefficients and metric, is
exactly the crossed Y_i X_j source form. Only the right input needs N4. -/
theorem canonicalNatFourOriginalOperator_decoded_rank_source (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator g) =
      ∑ ρ : RowIndex, ∑ i : Fin 9, ∑ j : Fin 9,
        star (natOccupationInner (rowThreeAuxiliarySeed ρ i*MvPolynomial.X j.val) f) *
          natOccupationInner (rowThreeAuxiliarySeed ρ j*MvPolynomial.X i.val) g := by
  rw [canonicalNatFourOriginalOperator_rank_form f g hNg]
  exact fourCanonical_original_terms_cross f g

#print axioms canonicalNatFourOriginalOperator_decoded_rank_source
end TorusLean.Shared.ThermalCoherentBosonRows
