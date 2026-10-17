import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck15 :
    ∀ r : OddMode 15, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 15 15 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 15

theorem originalFourRaiseCheck15 :
    ∀ T : Fin 24, ∀ r : OddMode 15, 15≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 15 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 15 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 15

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck15
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck15
