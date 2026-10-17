import torus.shared.FermionLocalJetFourCouplingFiniteComparisonTransport
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral01
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral02
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral03
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral04
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral05
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral06
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral07
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral08
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral09
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral10
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral11
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral12
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral13
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral14
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral15
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral16
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral17
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral18
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral19
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral20
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral21
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral22
import torus.shared.FermionLocalJetFourCouplingIntegerErrorLiteral23

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_comparison_certificate (d : Fin 23) :
    (((originalSlaterMatrixFin (d.val+1))ᴴ*originalSlaterMatrixFin (d.val+1)) *
      fourComparisonFinMatrix (d.val+1) *
      ((originalSlaterMatrixFin (d.val+1))ᴴ*originalSlaterMatrixFin (d.val+1))).PosSemidef := by
  exact original_four_comparison_certificate_of_error_literals
    originalIntegerErrorTableCheck01
    originalIntegerErrorTableCheck02
    originalIntegerErrorTableCheck03
    originalIntegerErrorTableCheck04
    originalIntegerErrorTableCheck05
    originalIntegerErrorTableCheck06
    originalIntegerErrorTableCheck07
    originalIntegerErrorTableCheck08
    originalIntegerErrorTableCheck09
    originalIntegerErrorTableCheck10
    originalIntegerErrorTableCheck11
    originalIntegerErrorTableCheck12
    originalIntegerErrorTableCheck13
    originalIntegerErrorTableCheck14
    originalIntegerErrorTableCheck15
    originalIntegerErrorTableCheck16
    originalIntegerErrorTableCheck17
    originalIntegerErrorTableCheck18
    originalIntegerErrorTableCheck19
    originalIntegerErrorTableCheck20
    originalIntegerErrorTableCheck21
    originalIntegerErrorTableCheck22
    originalIntegerErrorTableCheck23
    d

#print axioms fourComparisonFinMatrix_hermitian
#print axioms originalCopyRoot_middle
#print axioms original_four_compression_identity
#print axioms original_four_comparison_certificate
end TorusLean.Shared.FermionLocalJet.FourCoupling
