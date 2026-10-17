import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck12 :
    ∀ r : OddMode 12, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 12 12 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 12

theorem originalFourRaiseCheck12 :
    ∀ T : Fin 24, ∀ r : OddMode 12, 12≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 12 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 12 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 12

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck12
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck12
