import torus.shared.BosonFiniteCertificateNatFourDescendants411P2VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc2_compression_check :
    f411desc2ᵀ*f413rawM4Form*f411desc2=f411desc2Form := by
  have hD : natFourIntegerMatrix 2520 f411desc2IntegerCoordinatesShared=f411desc2 := by
    ext a b
    exact f411desc2_bounded_decode a b
  have hV : f411desc2IntegerCoordinatesSharedᵀ*f413rawInteger=f411desc2IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc2_bounded_v_row0 b
    · exact f411desc2_bounded_v_row1 b
    · exact f411desc2_bounded_v_row2 b
    · exact f411desc2_bounded_v_row3 b
  have hY : f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared=f411desc2IntegerFormShared := by
    ext a b
    exact f411desc2_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc2IntegerFormShared=f411desc2Form := by
    ext a b
    exact f411desc2_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f413rawInteger f411desc2IntegerCoordinatesShared f411desc2IntegerLeftProductShared f411desc2IntegerFormShared
    f413rawM4Form f411desc2 f411desc2Form f413_raw_integer_check hD hV hY hF

#print axioms f411desc2_compression_check

end TorusLean.BosonFiniteCertificate
