import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck05 :
    ∀ r : OddMode 5, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 5 5 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 5

theorem originalFourRaiseCheck05 :
    ∀ T : Fin 24, ∀ r : OddMode 5, 5≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 5 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 5 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 5

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck05
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck05
