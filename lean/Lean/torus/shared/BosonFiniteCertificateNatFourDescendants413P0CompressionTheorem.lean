import torus.shared.BosonFiniteCertificateNatFourDescendants413P0VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P0FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc0_compression_check :
    f413desc0ᵀ*f413rawM4Form*f413desc0=f413desc0Form := by
  have hD : natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared=f413desc0 := by
    ext a b
    exact f413desc0_bounded_decode a b
  have hV : f413desc0IntegerCoordinatesSharedᵀ*f413rawInteger=f413desc0IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f413desc0_bounded_v_row0 b
    · exact f413desc0_bounded_v_row1 b
    · exact f413desc0_bounded_v_row2 b
    · exact f413desc0_bounded_v_row3 b
    · exact f413desc0_bounded_v_row4 b
  have hY : f413desc0IntegerLeftProductShared*f413desc0IntegerCoordinatesShared=f413desc0IntegerFormShared := by
    ext a b
    exact f413desc0_bounded_product a b
  have hF : natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared=f413desc0Form := by
    ext a b
    exact f413desc0_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 27720
    f413rawInteger f413desc0IntegerCoordinatesShared f413desc0IntegerLeftProductShared f413desc0IntegerFormShared
    f413rawM4Form f413desc0 f413desc0Form f413_raw_integer_check hD hV hY hF

#print axioms f413desc0_compression_check

end TorusLean.BosonFiniteCertificate
