import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck08 :
    ∀ r : OddMode 8, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 8 8 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 8

theorem originalFourRaiseCheck08 :
    ∀ T : Fin 24, ∀ r : OddMode 8, 8≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 8 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 8 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 8

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck08
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck08
