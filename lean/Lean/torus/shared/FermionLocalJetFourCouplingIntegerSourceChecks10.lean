import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck10 :
    ∀ r : OddMode 10, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 10 10 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 10

theorem originalFourRaiseCheck10 :
    ∀ T : Fin 24, ∀ r : OddMode 10, 10≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 10 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 10 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 10

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck10
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck10
