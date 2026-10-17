import torus.shared.BosonFiniteCertificateNatFourDescendants410AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410_COM_average_check :
    (∑ k ∈ Finset.range 7, natFourOriginalCOMWeight k • f410descForms k)=b410average := by
  ext a b
  exact f410_bounded_average a b

#print axioms f410_COM_average_check

end TorusLean.BosonFiniteCertificate
