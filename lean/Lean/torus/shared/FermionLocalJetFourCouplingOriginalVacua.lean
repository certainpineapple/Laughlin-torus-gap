import torus.shared.FermionLocalJetFourCouplingIntegerWordActions
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks01
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks02
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks03
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks04
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks05
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks06
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks07
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks08
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks09
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks10
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks11
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks12
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks13
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks14
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks15
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks16
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks17
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks18
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks19
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks20
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks21
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks22
import torus.shared.FermionLocalJetFourCouplingIntegerSourceChecks23

/-! Actual original coupled vacua for all23 required degrees. Every finite
check is an explicit original integer-source arithmetic proof, not a premise. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionCOMWords

theorem original_coupled_vacuum (d : Fin 23) (r : OddMode (d.val+1)) :
    IsExteriorVacuum 4 (highestCoupledWords (d.val+1) r) := by
  apply original_coupled_vacuum_of_integer_check
  fin_cases d
  · exact originalFourVacuumCheck01 r
  · exact originalFourVacuumCheck02 r
  · exact originalFourVacuumCheck03 r
  · exact originalFourVacuumCheck04 r
  · exact originalFourVacuumCheck05 r
  · exact originalFourVacuumCheck06 r
  · exact originalFourVacuumCheck07 r
  · exact originalFourVacuumCheck08 r
  · exact originalFourVacuumCheck09 r
  · exact originalFourVacuumCheck10 r
  · exact originalFourVacuumCheck11 r
  · exact originalFourVacuumCheck12 r
  · exact originalFourVacuumCheck13 r
  · exact originalFourVacuumCheck14 r
  · exact originalFourVacuumCheck15 r
  · exact originalFourVacuumCheck16 r
  · exact originalFourVacuumCheck17 r
  · exact originalFourVacuumCheck18 r
  · exact originalFourVacuumCheck19 r
  · exact originalFourVacuumCheck20 r
  · exact originalFourVacuumCheck21 r
  · exact originalFourVacuumCheck22 r
  · exact originalFourVacuumCheck23 r

/-- Entire original full-T raising family, for every sector used by K4. -/
theorem original_descendant_raise (d : Fin 23) (T : Fin 24)
    (r : OddMode (d.val+1)) (hDT : d.val+1≤T.val) (hT : T.val<23) :
    realize 4 (wordRaise 4 (descendantWords (d.val+1) T.val r.val.val)) =
      (2*(Real.sqrt (T.val-(d.val+1)+1:ℝ):ℂ)) •
        formalDescendantColumn (d.val+1) (T.val+1) r.val.val := by
  have hcheck : alternateIntegerFourWords (raiseIntegerFourWords
      (integerSourceWords (d.val+1) T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords (d.val+1) (T.val+1) r.val.val) := by
    fin_cases d
    · exact originalFourRaiseCheck01 T r hDT hT
    · exact originalFourRaiseCheck02 T r hDT hT
    · exact originalFourRaiseCheck03 T r hDT hT
    · exact originalFourRaiseCheck04 T r hDT hT
    · exact originalFourRaiseCheck05 T r hDT hT
    · exact originalFourRaiseCheck06 T r hDT hT
    · exact originalFourRaiseCheck07 T r hDT hT
    · exact originalFourRaiseCheck08 T r hDT hT
    · exact originalFourRaiseCheck09 T r hDT hT
    · exact originalFourRaiseCheck10 T r hDT hT
    · exact originalFourRaiseCheck11 T r hDT hT
    · exact originalFourRaiseCheck12 T r hDT hT
    · exact originalFourRaiseCheck13 T r hDT hT
    · exact originalFourRaiseCheck14 T r hDT hT
    · exact originalFourRaiseCheck15 T r hDT hT
    · exact originalFourRaiseCheck16 T r hDT hT
    · exact originalFourRaiseCheck17 T r hDT hT
    · exact originalFourRaiseCheck18 T r hDT hT
    · exact originalFourRaiseCheck19 T r hDT hT
    · exact originalFourRaiseCheck20 T r hDT hT
    · exact originalFourRaiseCheck21 T r hDT hT
    · exact originalFourRaiseCheck22 T r hDT hT
    · exact originalFourRaiseCheck23 T r hDT hT
  simpa only [Nat.cast_add,Nat.cast_one] using
    original_descendant_raise_of_integer_check (d.val+1) T.val r hDT hcheck

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_coupled_vacuum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_descendant_raise
