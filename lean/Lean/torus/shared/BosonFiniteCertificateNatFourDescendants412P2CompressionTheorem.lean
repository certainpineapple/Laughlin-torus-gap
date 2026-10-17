import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc2_compression_check :
    f412desc2ᵀ*f414rawM4Form*f412desc2=f412desc2Form := by
  have hD : natFourIntegerMatrix 6930 f412desc2IntegerCoordinatesShared=f412desc2 := by
    ext a b
    exact f412desc2_bounded_decode a b
  have hV : f412desc2IntegerCoordinatesSharedᵀ*f414rawInteger=f412desc2IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f412desc2_bounded_v_row0 b
    · exact f412desc2_bounded_v_row1 b
    · exact f412desc2_bounded_v_row2 b
    · exact f412desc2_bounded_v_row3 b
    · exact f412desc2_bounded_v_row4 b
    · exact f412desc2_bounded_v_row5 b
    · exact f412desc2_bounded_v_row6 b
  have hY : f412desc2IntegerLeftProductShared*f412desc2IntegerCoordinatesShared=f412desc2IntegerFormShared := by
    ext a b
    exact f412desc2_bounded_product a b
  have hF : natFourIntegerMatrix (6930*1000000000000000000000000*6930) f412desc2IntegerFormShared=f412desc2Form := by
    ext a b
    exact f412desc2_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6930
    f414rawInteger f412desc2IntegerCoordinatesShared f412desc2IntegerLeftProductShared f412desc2IntegerFormShared
    f414rawM4Form f412desc2 f412desc2Form f414_raw_integer_check hD hV hY hF

#print axioms f412desc2_compression_check

end TorusLean.BosonFiniteCertificate
