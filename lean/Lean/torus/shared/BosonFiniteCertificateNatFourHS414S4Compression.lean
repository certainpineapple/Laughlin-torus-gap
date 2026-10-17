import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows4
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows5
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows6
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionVRows7
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_relative_S4_compression :
    b414relativeᵀ*f414rawS4Form*b414relative=b414s := by
  have hM : natFourIntegerMatrix 4 f414S4CompressionInteger=f414rawS4Form := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 24
    · exact f414_S4Compression_hM_rows_0 a (by omega) h0 b
    exact f414_S4Compression_hM_rows_1 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 180180 f414S4CompressionCoordinates=b414relative := by
    ext a b
    have ha := a.isLt
    exact f414_S4Compression_hD_rows_0 a (by omega) (by omega) b
  have hV : f414S4CompressionCoordinatesᵀ*f414S4CompressionInteger=f414S4CompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 1
    · exact f414_S4Compression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 2
    · exact f414_S4Compression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 3
    · exact f414_S4Compression_hV_rows_2 a (by omega) h2 b
    by_cases h3 : a.val < 4
    · exact f414_S4Compression_hV_rows_3 a (by omega) h3 b
    by_cases h4 : a.val < 5
    · exact f414_S4Compression_hV_rows_4 a (by omega) h4 b
    by_cases h5 : a.val < 6
    · exact f414_S4Compression_hV_rows_5 a (by omega) h5 b
    by_cases h6 : a.val < 7
    · exact f414_S4Compression_hV_rows_6 a (by omega) h6 b
    exact f414_S4Compression_hV_rows_7 a (by omega) (by omega) b
  have hY : f414S4CompressionLeftProduct*f414S4CompressionCoordinates=f414S4CompressionResult := by
    ext a b
    have ha := a.isLt
    exact f414_S4Compression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult=b414s := by
    ext a b
    have ha := a.isLt
    exact f414_S4Compression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 4 180180
    f414S4CompressionInteger f414S4CompressionCoordinates f414S4CompressionLeftProduct f414S4CompressionResult
    f414rawS4Form b414relative b414s hM hD hV hY hF

theorem f414_actual_relative_S4_form (x y : Fin 8 → ℂ) :
    natOccupationInner (natFourWordBlock f414basis (complexify b414relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f414basis (complexify b414relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b414s *ᵥ y) :=
  natFour_operator_relative_matrix_form f414basis b414relative canonicalNatFourS4
    f414rawS4Form b414s f414_actual_raw_S4_matrix
    f414_relative_S4_compression x y

#print axioms f414_relative_S4_compression
#print axioms f414_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
