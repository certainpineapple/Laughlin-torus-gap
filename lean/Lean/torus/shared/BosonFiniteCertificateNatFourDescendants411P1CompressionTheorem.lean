import torus.shared.BosonFiniteCertificateNatFourDescendants411P1VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc1_compression_check :
    f411desc1ᵀ*f412rawM4Form*f411desc1=f411desc1Form := by
  have hD : natFourIntegerMatrix 2520 f411desc1IntegerCoordinatesShared=f411desc1 := by
    ext a b
    exact f411desc1_bounded_decode a b
  have hV : f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger=f411desc1IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc1_bounded_v_row0 b
    · exact f411desc1_bounded_v_row1 b
    · exact f411desc1_bounded_v_row2 b
    · exact f411desc1_bounded_v_row3 b
  have hY : f411desc1IntegerLeftProductShared*f411desc1IntegerCoordinatesShared=f411desc1IntegerFormShared := by
    ext a b
    exact f411desc1_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc1IntegerFormShared=f411desc1Form := by
    ext a b
    exact f411desc1_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f412rawInteger f411desc1IntegerCoordinatesShared f411desc1IntegerLeftProductShared f411desc1IntegerFormShared
    f412rawM4Form f411desc1 f411desc1Form f412_raw_integer_check hD hV hY hF

#print axioms f411desc1_compression_check

end TorusLean.BosonFiniteCertificate
