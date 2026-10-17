import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows4
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows5
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows6
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionVRows7
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_relative_H_compression :
    b414relativeᵀ*f414rawHForm*b414relative=b414h := by
  have hM : natFourIntegerMatrix 4 f414HCompressionInteger=f414rawHForm := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 24
    · exact f414_HCompression_hM_rows_0 a (by omega) h0 b
    exact f414_HCompression_hM_rows_1 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 180180 f414HCompressionCoordinates=b414relative := by
    ext a b
    have ha := a.isLt
    exact f414_HCompression_hD_rows_0 a (by omega) (by omega) b
  have hV : f414HCompressionCoordinatesᵀ*f414HCompressionInteger=f414HCompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 1
    · exact f414_HCompression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 2
    · exact f414_HCompression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 3
    · exact f414_HCompression_hV_rows_2 a (by omega) h2 b
    by_cases h3 : a.val < 4
    · exact f414_HCompression_hV_rows_3 a (by omega) h3 b
    by_cases h4 : a.val < 5
    · exact f414_HCompression_hV_rows_4 a (by omega) h4 b
    by_cases h5 : a.val < 6
    · exact f414_HCompression_hV_rows_5 a (by omega) h5 b
    by_cases h6 : a.val < 7
    · exact f414_HCompression_hV_rows_6 a (by omega) h6 b
    exact f414_HCompression_hV_rows_7 a (by omega) (by omega) b
  have hY : f414HCompressionLeftProduct*f414HCompressionCoordinates=f414HCompressionResult := by
    ext a b
    have ha := a.isLt
    exact f414_HCompression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (180180*4*180180) f414HCompressionResult=b414h := by
    ext a b
    have ha := a.isLt
    exact f414_HCompression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 4 180180
    f414HCompressionInteger f414HCompressionCoordinates f414HCompressionLeftProduct f414HCompressionResult
    f414rawHForm b414relative b414h hM hD hV hY hF

theorem f414_actual_relative_H_form (x y : Fin 8 → ℂ) :
    natOccupationInner (natFourWordBlock f414basis (complexify b414relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f414basis (complexify b414relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b414h *ᵥ y) :=
  natFour_operator_relative_matrix_form f414basis b414relative canonicalPairHamiltonianNat
    f414rawHForm b414h f414_actual_raw_H_matrix
    f414_relative_H_compression x y

#print axioms f414_relative_H_compression
#print axioms f414_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
