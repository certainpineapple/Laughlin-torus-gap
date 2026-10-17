import torus.shared.FermionLocalJetFourCouplingGeneralSourceChecks

/-! Algebraic proofs for the exact two original source-check statements.
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck20 :
    ∀ r : OddMode 20, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 20 20 r.val.val)) = 0 := by
  exact GeneralSourceChecksCandidate.originalFourVacuumCheck 20

theorem originalFourRaiseCheck20 :
    ∀ T : Fin 24, ∀ r : OddMode 20, 20≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 20 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 20 (T.val+1) r.val.val) := by
  exact GeneralSourceChecksCandidate.originalFourRaiseCheck 20

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourVacuumCheck20
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalFourRaiseCheck20
