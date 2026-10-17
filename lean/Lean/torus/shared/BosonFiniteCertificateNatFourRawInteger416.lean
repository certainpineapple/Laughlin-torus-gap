import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows0
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows1
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows2
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows3
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows4
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows5
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows6
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows7
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows8
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows9
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows10
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows11
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows12
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows13
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows14
import torus.shared.BosonFiniteCertificateNatFourRawInteger416Rows15

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

theorem f416_raw_integer_check :
    natFourIntegerMatrix 1000000000000000000000000 f416rawInteger=f416rawM4Form := by
  ext a b
  fin_cases a
  · exact f416_raw_integer_rows_block0.1 b
  · exact f416_raw_integer_rows_block0.2.1 b
  · exact f416_raw_integer_rows_block0.2.2.1 b
  · exact f416_raw_integer_rows_block0.2.2.2 b
  · exact f416_raw_integer_rows_block1.1 b
  · exact f416_raw_integer_rows_block1.2.1 b
  · exact f416_raw_integer_rows_block1.2.2.1 b
  · exact f416_raw_integer_rows_block1.2.2.2 b
  · exact f416_raw_integer_rows_block2.1 b
  · exact f416_raw_integer_rows_block2.2.1 b
  · exact f416_raw_integer_rows_block2.2.2.1 b
  · exact f416_raw_integer_rows_block2.2.2.2 b
  · exact f416_raw_integer_rows_block3.1 b
  · exact f416_raw_integer_rows_block3.2.1 b
  · exact f416_raw_integer_rows_block3.2.2.1 b
  · exact f416_raw_integer_rows_block3.2.2.2 b
  · exact f416_raw_integer_rows_block4.1 b
  · exact f416_raw_integer_rows_block4.2.1 b
  · exact f416_raw_integer_rows_block4.2.2.1 b
  · exact f416_raw_integer_rows_block4.2.2.2 b
  · exact f416_raw_integer_rows_block5.1 b
  · exact f416_raw_integer_rows_block5.2.1 b
  · exact f416_raw_integer_rows_block5.2.2.1 b
  · exact f416_raw_integer_rows_block5.2.2.2 b
  · exact f416_raw_integer_rows_block6.1 b
  · exact f416_raw_integer_rows_block6.2.1 b
  · exact f416_raw_integer_rows_block6.2.2.1 b
  · exact f416_raw_integer_rows_block6.2.2.2 b
  · exact f416_raw_integer_rows_block7.1 b
  · exact f416_raw_integer_rows_block7.2.1 b
  · exact f416_raw_integer_rows_block7.2.2.1 b
  · exact f416_raw_integer_rows_block7.2.2.2 b
  · exact f416_raw_integer_rows_block8.1 b
  · exact f416_raw_integer_rows_block8.2.1 b
  · exact f416_raw_integer_rows_block8.2.2.1 b
  · exact f416_raw_integer_rows_block8.2.2.2 b
  · exact f416_raw_integer_rows_block9.1 b
  · exact f416_raw_integer_rows_block9.2.1 b
  · exact f416_raw_integer_rows_block9.2.2.1 b
  · exact f416_raw_integer_rows_block9.2.2.2 b
  · exact f416_raw_integer_rows_block10.1 b
  · exact f416_raw_integer_rows_block10.2.1 b
  · exact f416_raw_integer_rows_block10.2.2.1 b
  · exact f416_raw_integer_rows_block10.2.2.2 b
  · exact f416_raw_integer_rows_block11.1 b
  · exact f416_raw_integer_rows_block11.2.1 b
  · exact f416_raw_integer_rows_block11.2.2.1 b
  · exact f416_raw_integer_rows_block11.2.2.2 b
  · exact f416_raw_integer_rows_block12.1 b
  · exact f416_raw_integer_rows_block12.2.1 b
  · exact f416_raw_integer_rows_block12.2.2.1 b
  · exact f416_raw_integer_rows_block12.2.2.2 b
  · exact f416_raw_integer_rows_block13.1 b
  · exact f416_raw_integer_rows_block13.2.1 b
  · exact f416_raw_integer_rows_block13.2.2.1 b
  · exact f416_raw_integer_rows_block13.2.2.2 b
  · exact f416_raw_integer_rows_block14.1 b
  · exact f416_raw_integer_rows_block14.2.1 b
  · exact f416_raw_integer_rows_block14.2.2.1 b
  · exact f416_raw_integer_rows_block14.2.2.2 b
  · exact f416_raw_integer_rows_block15.1 b
  · exact f416_raw_integer_rows_block15.2.1 b
  · exact f416_raw_integer_rows_block15.2.2.1 b
  · exact f416_raw_integer_rows_block15.2.2.2 b

#print axioms f416_raw_integer_check
end TorusLean.BosonFiniteCertificate
