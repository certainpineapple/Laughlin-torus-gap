import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc1_compression_check :
    f412desc1ᵀ*f413rawM4Form*f412desc1=f412desc1Form := by
  have hD : natFourIntegerMatrix 6930 f412desc1IntegerCoordinatesShared=f412desc1 := by
    ext a b
    exact f412desc1_bounded_decode a b
  have hV : f412desc1IntegerCoordinatesSharedᵀ*f413rawInteger=f412desc1IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f412desc1_bounded_v_row0 b
    · exact f412desc1_bounded_v_row1 b
    · exact f412desc1_bounded_v_row2 b
    · exact f412desc1_bounded_v_row3 b
    · exact f412desc1_bounded_v_row4 b
    · exact f412desc1_bounded_v_row5 b
    · exact f412desc1_bounded_v_row6 b
  have hY : f412desc1IntegerLeftProductShared*f412desc1IntegerCoordinatesShared=f412desc1IntegerFormShared := by
    ext a b
    exact f412desc1_bounded_product a b
  have hF : natFourIntegerMatrix (6930*1000000000000000000000000*6930) f412desc1IntegerFormShared=f412desc1Form := by
    ext a b
    exact f412desc1_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6930
    f413rawInteger f412desc1IntegerCoordinatesShared f412desc1IntegerLeftProductShared f412desc1IntegerFormShared
    f413rawM4Form f412desc1 f412desc1Form f413_raw_integer_check hD hV hY hF

#print axioms f412desc1_compression_check

end TorusLean.BosonFiniteCertificate
