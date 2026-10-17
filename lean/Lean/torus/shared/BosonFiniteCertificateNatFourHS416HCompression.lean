import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionMRows2
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionMRows3
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows4
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows5
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows6
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows7
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows8
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionVRows9
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionYRows1
import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_relative_H_compression :
    b416relativeᵀ*f416rawHForm*b416relative=b416h := by
  have hM : natFourIntegerMatrix 8 f416HCompressionInteger=f416rawHForm := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 16
    · exact f416_HCompression_hM_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 32
    · exact f416_HCompression_hM_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 48
    · exact f416_HCompression_hM_rows_2 a (by omega) h2 b
    exact f416_HCompression_hM_rows_3 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 180180 f416HCompressionCoordinates=b416relative := by
    ext a b
    have ha := a.isLt
    exact f416_HCompression_hD_rows_0 a (by omega) (by omega) b
  have hV : f416HCompressionCoordinatesᵀ*f416HCompressionInteger=f416HCompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 1
    · exact f416_HCompression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 2
    · exact f416_HCompression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 3
    · exact f416_HCompression_hV_rows_2 a (by omega) h2 b
    by_cases h3 : a.val < 4
    · exact f416_HCompression_hV_rows_3 a (by omega) h3 b
    by_cases h4 : a.val < 5
    · exact f416_HCompression_hV_rows_4 a (by omega) h4 b
    by_cases h5 : a.val < 6
    · exact f416_HCompression_hV_rows_5 a (by omega) h5 b
    by_cases h6 : a.val < 7
    · exact f416_HCompression_hV_rows_6 a (by omega) h6 b
    by_cases h7 : a.val < 8
    · exact f416_HCompression_hV_rows_7 a (by omega) h7 b
    by_cases h8 : a.val < 9
    · exact f416_HCompression_hV_rows_8 a (by omega) h8 b
    exact f416_HCompression_hV_rows_9 a (by omega) (by omega) b
  have hY : f416HCompressionLeftProduct*f416HCompressionCoordinates=f416HCompressionResult := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 5
    · exact f416_HCompression_hY_rows_0 a (by omega) h0 b
    exact f416_HCompression_hY_rows_1 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (180180*8*180180) f416HCompressionResult=b416h := by
    ext a b
    have ha := a.isLt
    exact f416_HCompression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 8 180180
    f416HCompressionInteger f416HCompressionCoordinates f416HCompressionLeftProduct f416HCompressionResult
    f416rawHForm b416relative b416h hM hD hV hY hF

theorem f416_actual_relative_H_form (x y : Fin 10 → ℂ) :
    natOccupationInner (natFourWordBlock f416basis (complexify b416relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f416basis (complexify b416relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b416h *ᵥ y) :=
  natFour_operator_relative_matrix_form f416basis b416relative canonicalPairHamiltonianNat
    f416rawHForm b416h f416_actual_raw_H_matrix
    f416_relative_H_compression x y

#print axioms f416_relative_H_compression
#print axioms f416_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
