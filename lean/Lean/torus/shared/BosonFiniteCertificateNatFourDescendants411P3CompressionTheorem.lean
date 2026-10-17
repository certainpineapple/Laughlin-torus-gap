import torus.shared.BosonFiniteCertificateNatFourDescendants411P3VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc3_compression_check :
    f411desc3ᵀ*f414rawM4Form*f411desc3=f411desc3Form := by
  have hD : natFourIntegerMatrix 2520 f411desc3IntegerCoordinatesShared=f411desc3 := by
    ext a b
    exact f411desc3_bounded_decode a b
  have hV : f411desc3IntegerCoordinatesSharedᵀ*f414rawInteger=f411desc3IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc3_bounded_v_row0 b
    · exact f411desc3_bounded_v_row1 b
    · exact f411desc3_bounded_v_row2 b
    · exact f411desc3_bounded_v_row3 b
  have hY : f411desc3IntegerLeftProductShared*f411desc3IntegerCoordinatesShared=f411desc3IntegerFormShared := by
    ext a b
    exact f411desc3_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc3IntegerFormShared=f411desc3Form := by
    ext a b
    exact f411desc3_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f414rawInteger f411desc3IntegerCoordinatesShared f411desc3IntegerLeftProductShared f411desc3IntegerFormShared
    f414rawM4Form f411desc3 f411desc3Form f414_raw_integer_check hD hV hY hF

#print axioms f411desc3_compression_check

end TorusLean.BosonFiniteCertificate
