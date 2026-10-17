import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck04 :
    ∀ r : OddMode 4, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 4 4 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 4

theorem originalFourRaiseCheck04 :
    ∀ T : Fin 24, ∀ r : OddMode 4, 4≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 4 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 4 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 4

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck04
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck04
