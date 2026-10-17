import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc4_compression_check :
    f412desc4ᵀ*f416rawM4Form*f412desc4=f412desc4Form := by
  have hD : natFourIntegerMatrix 6930 f412desc4IntegerCoordinatesShared=f412desc4 := by
    ext a b
    exact f412desc4_bounded_decode a b
  have hV : f412desc4IntegerCoordinatesSharedᵀ*f416rawInteger=f412desc4IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f412desc4_bounded_v_row0 b
    · exact f412desc4_bounded_v_row1 b
    · exact f412desc4_bounded_v_row2 b
    · exact f412desc4_bounded_v_row3 b
    · exact f412desc4_bounded_v_row4 b
    · exact f412desc4_bounded_v_row5 b
    · exact f412desc4_bounded_v_row6 b
  have hY : f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared=f412desc4IntegerFormShared := by
    ext a b
    exact f412desc4_bounded_product a b
  have hF : natFourIntegerMatrix (6930*1000000000000000000000000*6930) f412desc4IntegerFormShared=f412desc4Form := by
    ext a b
    exact f412desc4_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6930
    f416rawInteger f412desc4IntegerCoordinatesShared f412desc4IntegerLeftProductShared f412desc4IntegerFormShared
    f416rawM4Form f412desc4 f412desc4Form f416_raw_integer_check hD hV hY hF

#print axioms f412desc4_compression_check

end TorusLean.BosonFiniteCertificate
