import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_relative_H_compression :
    b413relativeᵀ*f413rawHForm*b413relative=b413h := by
  have hM : natFourIntegerMatrix 2 f413HCompressionInteger=f413rawHForm := by
    ext a b
    have ha := a.isLt
    exact f413_HCompression_hM_rows_0 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 27720 f413HCompressionCoordinates=b413relative := by
    ext a b
    have ha := a.isLt
    exact f413_HCompression_hD_rows_0 a (by omega) (by omega) b
  have hV : f413HCompressionCoordinatesᵀ*f413HCompressionInteger=f413HCompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 2
    · exact f413_HCompression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 4
    · exact f413_HCompression_hV_rows_1 a (by omega) h1 b
    exact f413_HCompression_hV_rows_2 a (by omega) (by omega) b
  have hY : f413HCompressionLeftProduct*f413HCompressionCoordinates=f413HCompressionResult := by
    ext a b
    have ha := a.isLt
    exact f413_HCompression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (27720*2*27720) f413HCompressionResult=b413h := by
    ext a b
    have ha := a.isLt
    exact f413_HCompression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 2 27720
    f413HCompressionInteger f413HCompressionCoordinates f413HCompressionLeftProduct f413HCompressionResult
    f413rawHForm b413relative b413h hM hD hV hY hF

theorem f413_actual_relative_H_form (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f413basis (complexify b413relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f413basis (complexify b413relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b413h *ᵥ y) :=
  natFour_operator_relative_matrix_form f413basis b413relative canonicalPairHamiltonianNat
    f413rawHForm b413h f413_actual_raw_H_matrix
    f413_relative_H_compression x y

#print axioms f413_relative_H_compression
#print axioms f413_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
