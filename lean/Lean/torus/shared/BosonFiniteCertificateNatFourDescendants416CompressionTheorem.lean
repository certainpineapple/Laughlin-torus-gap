import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows4
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows5
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows6
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows7
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows8
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionVRows9
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionYRows1
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f416desc0_compression_check :
    f416desc0ᵀ*f416rawM4Form*f416desc0=f416desc0Form := by
  have hD : natFourIntegerMatrix 180180 f416DescCompressionCoordinates=f416desc0 := by
    ext a b
    have ha := a.isLt
    exact f416_DescCompression_hD_rows_0 a (by omega) (by omega) b
  have hV : f416DescCompressionCoordinatesᵀ*f416rawInteger=f416DescCompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 1
    · exact f416_DescCompression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 2
    · exact f416_DescCompression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 3
    · exact f416_DescCompression_hV_rows_2 a (by omega) h2 b
    by_cases h3 : a.val < 4
    · exact f416_DescCompression_hV_rows_3 a (by omega) h3 b
    by_cases h4 : a.val < 5
    · exact f416_DescCompression_hV_rows_4 a (by omega) h4 b
    by_cases h5 : a.val < 6
    · exact f416_DescCompression_hV_rows_5 a (by omega) h5 b
    by_cases h6 : a.val < 7
    · exact f416_DescCompression_hV_rows_6 a (by omega) h6 b
    by_cases h7 : a.val < 8
    · exact f416_DescCompression_hV_rows_7 a (by omega) h7 b
    by_cases h8 : a.val < 9
    · exact f416_DescCompression_hV_rows_8 a (by omega) h8 b
    exact f416_DescCompression_hV_rows_9 a (by omega) (by omega) b
  have hY : f416DescCompressionLeftProduct*f416DescCompressionCoordinates=f416DescCompressionResult := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 5
    · exact f416_DescCompression_hY_rows_0 a (by omega) h0 b
    exact f416_DescCompression_hY_rows_1 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult=f416desc0Form := by
    ext a b
    have ha := a.isLt
    exact f416_DescCompression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 180180
    f416rawInteger f416DescCompressionCoordinates f416DescCompressionLeftProduct f416DescCompressionResult
    f416rawM4Form f416desc0 f416desc0Form f416_raw_integer_check hD hV hY hF


#print axioms f416desc0_compression_check

end TorusLean.BosonFiniteCertificate
