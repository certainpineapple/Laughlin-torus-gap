import torus.shared.BosonFiniteCertificateNatFourDescendants414AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_COM_average_check :
    (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k)=b414average := by
  ext a b
  exact f414_bounded_average a b

#print axioms f414_COM_average_check

end TorusLean.BosonFiniteCertificate
