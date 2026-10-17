import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionMRows2
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionMRows3
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows4
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows5
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows6
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows7
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows8
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionVRows9
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionYRows1
import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_relative_S4_compression :
    b416relativeᵀ*f416rawS4Form*b416relative=b416s := by
  have hM : natFourIntegerMatrix 4 f416S4CompressionInteger=f416rawS4Form := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 16
    · exact f416_S4Compression_hM_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 32
    · exact f416_S4Compression_hM_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 48
    · exact f416_S4Compression_hM_rows_2 a (by omega) h2 b
    exact f416_S4Compression_hM_rows_3 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 180180 f416S4CompressionCoordinates=b416relative := by
    ext a b
    have ha := a.isLt
    exact f416_S4Compression_hD_rows_0 a (by omega) (by omega) b
  have hV : f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger=f416S4CompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 1
    · exact f416_S4Compression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 2
    · exact f416_S4Compression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 3
    · exact f416_S4Compression_hV_rows_2 a (by omega) h2 b
    by_cases h3 : a.val < 4
    · exact f416_S4Compression_hV_rows_3 a (by omega) h3 b
    by_cases h4 : a.val < 5
    · exact f416_S4Compression_hV_rows_4 a (by omega) h4 b
    by_cases h5 : a.val < 6
    · exact f416_S4Compression_hV_rows_5 a (by omega) h5 b
    by_cases h6 : a.val < 7
    · exact f416_S4Compression_hV_rows_6 a (by omega) h6 b
    by_cases h7 : a.val < 8
    · exact f416_S4Compression_hV_rows_7 a (by omega) h7 b
    by_cases h8 : a.val < 9
    · exact f416_S4Compression_hV_rows_8 a (by omega) h8 b
    exact f416_S4Compression_hV_rows_9 a (by omega) (by omega) b
  have hY : f416S4CompressionLeftProduct*f416S4CompressionCoordinates=f416S4CompressionResult := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 5
    · exact f416_S4Compression_hY_rows_0 a (by omega) h0 b
    exact f416_S4Compression_hY_rows_1 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult=b416s := by
    ext a b
    have ha := a.isLt
    exact f416_S4Compression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 4 180180
    f416S4CompressionInteger f416S4CompressionCoordinates f416S4CompressionLeftProduct f416S4CompressionResult
    f416rawS4Form b416relative b416s hM hD hV hY hF

theorem f416_actual_relative_S4_form (x y : Fin 10 → ℂ) :
    natOccupationInner (natFourWordBlock f416basis (complexify b416relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f416basis (complexify b416relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b416s *ᵥ y) :=
  natFour_operator_relative_matrix_form f416basis b416relative canonicalNatFourS4
    f416rawS4Form b416s f416_actual_raw_S4_matrix
    f416_relative_S4_compression x y

#print axioms f416_relative_S4_compression
#print axioms f416_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
