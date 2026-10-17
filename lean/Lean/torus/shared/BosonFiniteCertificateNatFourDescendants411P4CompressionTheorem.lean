import torus.shared.BosonFiniteCertificateNatFourDescendants411P4VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc4_compression_check :
    f411desc4ᵀ*f415rawM4Form*f411desc4=f411desc4Form := by
  have hD : natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared=f411desc4 := by
    ext a b
    exact f411desc4_bounded_decode a b
  have hV : f411desc4IntegerCoordinatesSharedᵀ*f415rawInteger=f411desc4IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc4_bounded_v_row0 b
    · exact f411desc4_bounded_v_row1 b
    · exact f411desc4_bounded_v_row2 b
    · exact f411desc4_bounded_v_row3 b
  have hY : f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared=f411desc4IntegerFormShared := by
    ext a b
    exact f411desc4_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared=f411desc4Form := by
    ext a b
    exact f411desc4_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f415rawInteger f411desc4IntegerCoordinatesShared f411desc4IntegerLeftProductShared f411desc4IntegerFormShared
    f415rawM4Form f411desc4 f411desc4Form f415_raw_integer_check hD hV hY hF

#print axioms f411desc4_compression_check

end TorusLean.BosonFiniteCertificate
