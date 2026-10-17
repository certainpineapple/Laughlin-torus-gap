import torus.shared.BosonFiniteCertificateNatFourCOMOriginalDegreeCases
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD00
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD01
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD02
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD03
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD04
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD05
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD06
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD07
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD08
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD09
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD10
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD11
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD12
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD13
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD14
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD15
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawFormsD16

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem canonicalNatFourOriginalOperator_all_raw_matrix_forms (D : Fin 17)
    (x y : Fin (natFourOccupationDimension D) → ℂ) :
    natOccupationInner (natFourWordBlock (natFourOccupationBasis D) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis D) y))=
        star x ⬝ᵥ (complexify (natFourOriginalRawFormMatrix D) *ᵥ y) := by
  exact natFourFinSeventeen_cases
    (fun d : Fin 17 => ∀ u v : Fin (natFourOccupationDimension d) → ℂ,
      natOccupationInner (natFourWordBlock (natFourOccupationBasis d) u)
        (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis d) v))=
          star u ⬝ᵥ (complexify (natFourOriginalRawFormMatrix d) *ᵥ v))
    canonicalNatFourOriginalOperator_raw_matrix_form_D00
    canonicalNatFourOriginalOperator_raw_matrix_form_D01
    canonicalNatFourOriginalOperator_raw_matrix_form_D02
    canonicalNatFourOriginalOperator_raw_matrix_form_D03
    canonicalNatFourOriginalOperator_raw_matrix_form_D04
    canonicalNatFourOriginalOperator_raw_matrix_form_D05
    canonicalNatFourOriginalOperator_raw_matrix_form_D06
    canonicalNatFourOriginalOperator_raw_matrix_form_D07
    canonicalNatFourOriginalOperator_raw_matrix_form_D08
    canonicalNatFourOriginalOperator_raw_matrix_form_D09
    canonicalNatFourOriginalOperator_raw_matrix_form_D10
    canonicalNatFourOriginalOperator_raw_matrix_form_D11
    canonicalNatFourOriginalOperator_raw_matrix_form_D12
    canonicalNatFourOriginalOperator_raw_matrix_form_D13
    canonicalNatFourOriginalOperator_raw_matrix_form_D14
    canonicalNatFourOriginalOperator_raw_matrix_form_D15
    canonicalNatFourOriginalOperator_raw_matrix_form_D16
    D x y

#print axioms canonicalNatFourOriginalOperator_all_raw_matrix_forms
end TorusLean.BosonFiniteCertificate
