import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionMRows2
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_relative_S4_compression :
    b415relativeᵀ*f415rawS4Form*b415relative=b415s := by
  have hM : natFourIntegerMatrix 2 f415S4CompressionInteger=f415rawS4Form := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 18
    · exact f415_S4Compression_hM_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 36
    · exact f415_S4Compression_hM_rows_1 a (by omega) h1 b
    exact f415_S4Compression_hM_rows_2 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 360360 f415S4CompressionCoordinates=b415relative := by
    ext a b
    have ha := a.isLt
    exact f415_S4Compression_hD_rows_0 a (by omega) (by omega) b
  have hV : f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger=f415S4CompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 2
    · exact f415_S4Compression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 4
    · exact f415_S4Compression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 6
    · exact f415_S4Compression_hV_rows_2 a (by omega) h2 b
    exact f415_S4Compression_hV_rows_3 a (by omega) (by omega) b
  have hY : f415S4CompressionLeftProduct*f415S4CompressionCoordinates=f415S4CompressionResult := by
    ext a b
    have ha := a.isLt
    exact f415_S4Compression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult=b415s := by
    ext a b
    have ha := a.isLt
    exact f415_S4Compression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 2 360360
    f415S4CompressionInteger f415S4CompressionCoordinates f415S4CompressionLeftProduct f415S4CompressionResult
    f415rawS4Form b415relative b415s hM hD hV hY hF

theorem f415_actual_relative_S4_form (x y : Fin 7 → ℂ) :
    natOccupationInner (natFourWordBlock f415basis (complexify b415relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f415basis (complexify b415relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b415s *ᵥ y) :=
  natFour_operator_relative_matrix_form f415basis b415relative canonicalNatFourS4
    f415rawS4Form b415s f415_actual_raw_S4_matrix
    f415_relative_S4_compression x y

#print axioms f415_relative_S4_compression
#print axioms f415_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
