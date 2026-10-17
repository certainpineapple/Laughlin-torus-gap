import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck16 :
    ∀ r : OddMode 16, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 16 16 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 16

theorem originalFourRaiseCheck16 :
    ∀ T : Fin 24, ∀ r : OddMode 16, 16≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 16 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 16 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 16

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck16
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck16
