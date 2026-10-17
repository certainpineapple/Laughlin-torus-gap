import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2VRow7
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc2_compression_check :
    f414desc2ᵀ*f416rawM4Form*f414desc2=f414desc2Form := by
  have hD : natFourIntegerMatrix 180180 f414desc2IntegerCoordinatesShared=f414desc2 := by
    ext a b
    exact f414desc2_bounded_decode a b
  have hV : f414desc2IntegerCoordinatesSharedᵀ*f416rawInteger=f414desc2IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f414desc2_bounded_v_row0 b
    · exact f414desc2_bounded_v_row1 b
    · exact f414desc2_bounded_v_row2 b
    · exact f414desc2_bounded_v_row3 b
    · exact f414desc2_bounded_v_row4 b
    · exact f414desc2_bounded_v_row5 b
    · exact f414desc2_bounded_v_row6 b
    · exact f414desc2_bounded_v_row7 b
  have hY : f414desc2IntegerLeftProductShared*f414desc2IntegerCoordinatesShared=f414desc2IntegerFormShared := by
    ext a b
    exact f414desc2_bounded_product a b
  have hF : natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc2IntegerFormShared=f414desc2Form := by
    ext a b
    exact f414desc2_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 180180
    f416rawInteger f414desc2IntegerCoordinatesShared f414desc2IntegerLeftProductShared f414desc2IntegerFormShared
    f416rawM4Form f414desc2 f414desc2Form f416_raw_integer_check hD hV hY hF

#print axioms f414desc2_compression_check

end TorusLean.BosonFiniteCertificate
