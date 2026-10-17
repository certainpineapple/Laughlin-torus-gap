import torus.shared.BosonFiniteCertificateNatFourDescendants413P2VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc2_compression_check :
    f413desc2ᵀ*f415rawM4Form*f413desc2=f413desc2Form := by
  have hD : natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared=f413desc2 := by
    ext a b
    exact f413desc2_bounded_decode a b
  have hV : f413desc2IntegerCoordinatesSharedᵀ*f415rawInteger=f413desc2IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f413desc2_bounded_v_row0 b
    · exact f413desc2_bounded_v_row1 b
    · exact f413desc2_bounded_v_row2 b
    · exact f413desc2_bounded_v_row3 b
    · exact f413desc2_bounded_v_row4 b
  have hY : f413desc2IntegerLeftProductShared*f413desc2IntegerCoordinatesShared=f413desc2IntegerFormShared := by
    ext a b
    exact f413desc2_bounded_product a b
  have hF : natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc2IntegerFormShared=f413desc2Form := by
    ext a b
    exact f413desc2_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 27720
    f415rawInteger f413desc2IntegerCoordinatesShared f413desc2IntegerLeftProductShared f413desc2IntegerFormShared
    f415rawM4Form f413desc2 f413desc2Form f415_raw_integer_check hD hV hY hF

#print axioms f413desc2_compression_check

end TorusLean.BosonFiniteCertificate
