import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0VRow7
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants414P0FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc0_compression_check :
    f414desc0ᵀ*f414rawM4Form*f414desc0=f414desc0Form := by
  have hD : natFourIntegerMatrix 180180 f414desc0IntegerCoordinatesShared=f414desc0 := by
    ext a b
    exact f414desc0_bounded_decode a b
  have hV : f414desc0IntegerCoordinatesSharedᵀ*f414rawInteger=f414desc0IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f414desc0_bounded_v_row0 b
    · exact f414desc0_bounded_v_row1 b
    · exact f414desc0_bounded_v_row2 b
    · exact f414desc0_bounded_v_row3 b
    · exact f414desc0_bounded_v_row4 b
    · exact f414desc0_bounded_v_row5 b
    · exact f414desc0_bounded_v_row6 b
    · exact f414desc0_bounded_v_row7 b
  have hY : f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared=f414desc0IntegerFormShared := by
    ext a b
    exact f414desc0_bounded_product a b
  have hF : natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc0IntegerFormShared=f414desc0Form := by
    ext a b
    exact f414desc0_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 180180
    f414rawInteger f414desc0IntegerCoordinatesShared f414desc0IntegerLeftProductShared f414desc0IntegerFormShared
    f414rawM4Form f414desc0 f414desc0Form f414_raw_integer_check hD hV hY hF

#print axioms f414desc0_compression_check

end TorusLean.BosonFiniteCertificate
