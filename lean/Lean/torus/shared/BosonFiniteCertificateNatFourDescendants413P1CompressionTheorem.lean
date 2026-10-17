import torus.shared.BosonFiniteCertificateNatFourDescendants413P1VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc1_compression_check :
    f413desc1ᵀ*f414rawM4Form*f413desc1=f413desc1Form := by
  have hD : natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared=f413desc1 := by
    ext a b
    exact f413desc1_bounded_decode a b
  have hV : f413desc1IntegerCoordinatesSharedᵀ*f414rawInteger=f413desc1IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f413desc1_bounded_v_row0 b
    · exact f413desc1_bounded_v_row1 b
    · exact f413desc1_bounded_v_row2 b
    · exact f413desc1_bounded_v_row3 b
    · exact f413desc1_bounded_v_row4 b
  have hY : f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared=f413desc1IntegerFormShared := by
    ext a b
    exact f413desc1_bounded_product a b
  have hF : natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc1IntegerFormShared=f413desc1Form := by
    ext a b
    exact f413desc1_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 27720
    f414rawInteger f413desc1IntegerCoordinatesShared f413desc1IntegerLeftProductShared f413desc1IntegerFormShared
    f414rawM4Form f413desc1 f413desc1Form f414_raw_integer_check hD hV hY hF

#print axioms f413desc1_compression_check

end TorusLean.BosonFiniteCertificate
