import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionMRows0
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionMRows1
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionMRows2
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionDRows0
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionVRows0
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionVRows1
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionVRows2
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionVRows3
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionYRows0
import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_relative_H_compression :
    b415relativeᵀ*f415rawHForm*b415relative=b415h := by
  have hM : natFourIntegerMatrix 4 f415HCompressionInteger=f415rawHForm := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 18
    · exact f415_HCompression_hM_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 36
    · exact f415_HCompression_hM_rows_1 a (by omega) h1 b
    exact f415_HCompression_hM_rows_2 a (by omega) (by omega) b
  have hD : natFourIntegerMatrix 360360 f415HCompressionCoordinates=b415relative := by
    ext a b
    have ha := a.isLt
    exact f415_HCompression_hD_rows_0 a (by omega) (by omega) b
  have hV : f415HCompressionCoordinatesᵀ*f415HCompressionInteger=f415HCompressionLeftProduct := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 2
    · exact f415_HCompression_hV_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 4
    · exact f415_HCompression_hV_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 6
    · exact f415_HCompression_hV_rows_2 a (by omega) h2 b
    exact f415_HCompression_hV_rows_3 a (by omega) (by omega) b
  have hY : f415HCompressionLeftProduct*f415HCompressionCoordinates=f415HCompressionResult := by
    ext a b
    have ha := a.isLt
    exact f415_HCompression_hY_rows_0 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (360360*4*360360) f415HCompressionResult=b415h := by
    ext a b
    have ha := a.isLt
    exact f415_HCompression_hF_rows_0 a (by omega) (by omega) b
  exact natFourIntegerMatrix_compression_check_staged 4 360360
    f415HCompressionInteger f415HCompressionCoordinates f415HCompressionLeftProduct f415HCompressionResult
    f415rawHForm b415relative b415h hM hD hV hY hF

theorem f415_actual_relative_H_form (x y : Fin 7 → ℂ) :
    natOccupationInner (natFourWordBlock f415basis (complexify b415relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f415basis (complexify b415relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b415h *ᵥ y) :=
  natFour_operator_relative_matrix_form f415basis b415relative canonicalPairHamiltonianNat
    f415rawHForm b415h f415_actual_raw_H_matrix
    f415_relative_H_compression x y

#print axioms f415_relative_H_compression
#print axioms f415_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
