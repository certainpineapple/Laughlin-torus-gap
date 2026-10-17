import torus.shared.FermionLocalJetFourCouplingSlaterGram
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck06
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck08
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck10
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck12
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck14
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck16
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck18
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck19
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck20
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck21
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck22
import torus.shared.FermionLocalJetFourCouplingSlaterSourceListCheck23

/-! All original degrees and odd copies; this consumes actual finite source
checks rather than assuming the manuscript source/Gram identification. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

theorem original_coupled_slater (d : Fin 23) (r : OddMode (d.val+1)) :
    formalCoupledColumn (d.val+1) r =
      ∑ A : SlaterIndex (d.val+1),
        originalSlaterMatrix (d.val+1) A r • formalSlater (d.val+1) A := by
  apply original_coupled_slater_of_integer_check
  fin_cases d
  · exact originalSlaterSourceCheck01
  · exact originalSlaterSourceCheck02
  · exact originalSlaterSourceCheck03
  · exact originalSlaterSourceCheck04
  · exact originalSlaterSourceCheck05
  · exact originalSlaterSourceCheck06
  · exact originalSlaterSourceCheck07
  · exact originalSlaterSourceCheck08
  · exact originalSlaterSourceCheck09
  · exact originalSlaterSourceCheck10
  · exact originalSlaterSourceCheck11
  · exact originalSlaterSourceCheck12
  · exact originalSlaterSourceCheck13
  · exact originalSlaterSourceCheck14
  · exact originalSlaterSourceCheck15
  · exact originalSlaterSourceCheck16
  · exact originalSlaterSourceCheck17
  · exact originalSlaterSourceCheck18
  · exact originalSlaterSourceCheck19
  · exact originalSlaterSourceCheck20
  · exact originalSlaterSourceCheck21
  · exact originalSlaterSourceCheck22
  · exact originalSlaterSourceCheck23

#print axioms original_coupled_slater
end TorusLean.Shared.FermionLocalJet.FourCoupling
