import torus.shared.BosonFiniteCertificateNatFourDescendants413P3VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc3_compression_check :
    f413desc3ᵀ*f416rawM4Form*f413desc3=f413desc3Form := by
  have hD : natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared=f413desc3 := by
    ext a b
    exact f413desc3_bounded_decode a b
  have hV : f413desc3IntegerCoordinatesSharedᵀ*f416rawInteger=f413desc3IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f413desc3_bounded_v_row0 b
    · exact f413desc3_bounded_v_row1 b
    · exact f413desc3_bounded_v_row2 b
    · exact f413desc3_bounded_v_row3 b
    · exact f413desc3_bounded_v_row4 b
  have hY : f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared=f413desc3IntegerFormShared := by
    ext a b
    exact f413desc3_bounded_product a b
  have hF : natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc3IntegerFormShared=f413desc3Form := by
    ext a b
    exact f413desc3_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 27720
    f416rawInteger f413desc3IntegerCoordinatesShared f413desc3IntegerLeftProductShared f413desc3IntegerFormShared
    f416rawM4Form f413desc3 f413desc3Form f416_raw_integer_check hD hV hY hF

#print axioms f413desc3_compression_check

end TorusLean.BosonFiniteCertificate
