import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1VRow7
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc1_compression_check :
    f414desc1ᵀ*f415rawM4Form*f414desc1=f414desc1Form := by
  have hD : natFourIntegerMatrix 180180 f414desc1IntegerCoordinatesShared=f414desc1 := by
    ext a b
    exact f414desc1_bounded_decode a b
  have hV : f414desc1IntegerCoordinatesSharedᵀ*f415rawInteger=f414desc1IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f414desc1_bounded_v_row0 b
    · exact f414desc1_bounded_v_row1 b
    · exact f414desc1_bounded_v_row2 b
    · exact f414desc1_bounded_v_row3 b
    · exact f414desc1_bounded_v_row4 b
    · exact f414desc1_bounded_v_row5 b
    · exact f414desc1_bounded_v_row6 b
    · exact f414desc1_bounded_v_row7 b
  have hY : f414desc1IntegerLeftProductShared*f414desc1IntegerCoordinatesShared=f414desc1IntegerFormShared := by
    ext a b
    exact f414desc1_bounded_product a b
  have hF : natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared=f414desc1Form := by
    ext a b
    exact f414desc1_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 180180
    f415rawInteger f414desc1IntegerCoordinatesShared f414desc1IntegerLeftProductShared f414desc1IntegerFormShared
    f415rawM4Form f414desc1 f414desc1Form f415_raw_integer_check hD hV hY hF

#print axioms f414desc1_compression_check

end TorusLean.BosonFiniteCertificate
