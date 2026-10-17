import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_relative_S4_compression :
    b413relativeᵀ*f413rawS4Form*b413relative=b413s := by
  have hM : natFourIntegerMatrix 4 f413S4CompressionInteger=f413rawS4Form := by
    ext a b
    have ha := a.isLt
    exact f413_S4Compression_hM_rows_0 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 27720 f413S4CompressionCoordinates=b413relative := by
    ext a b
    have ha := a.isLt
    exact f413_S4Compression_hD_rows_0 a (by omega) (by omega) b
  have hV : f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger=f413S4CompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 2
    · exact f413_S4Compression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 4
    · exact f413_S4Compression_hV_rows_1 a (by omega) h1 b
    exact f413_S4Compression_hV_rows_2 a (by omega) (by omega) b
  have hY : f413S4CompressionLeftProduct*f413S4CompressionCoordinates=f413S4CompressionResult := by
    ext a b
    have ha := a.isLt
    exact f413_S4Compression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult=b413s := by
    ext a b
    have ha := a.isLt
    exact f413_S4Compression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 4 27720
    f413S4CompressionInteger f413S4CompressionCoordinates f413S4CompressionLeftProduct f413S4CompressionResult
    f413rawS4Form b413relative b413s hM hD hV hY hF

theorem f413_actual_relative_S4_form (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f413basis (complexify b413relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f413basis (complexify b413relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b413s *ᵥ y) :=
  natFour_operator_relative_matrix_form f413basis b413relative canonicalNatFourS4
    f413rawS4Form b413s f413_actual_raw_S4_matrix
    f413_relative_S4_compression x y

#print axioms f413_relative_S4_compression
#print axioms f413_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
