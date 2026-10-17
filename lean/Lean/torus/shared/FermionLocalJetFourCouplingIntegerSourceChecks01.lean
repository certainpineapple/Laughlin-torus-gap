import torus.shared.FermionLocalJetFourCouplingDegreeOneLadderBridge01

/- Canonical original SourceChecks01 declarations, with unchanged complete statements.
The proofs use the degree-one algebraic helpers after their ordinary acceptance. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalFourVacuumCheck01 :
    ∀ r : OddMode 1, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 1 1 r.val.val)) = 0 := by
  exact DegreeOneLadderBridgeCandidate.originalFourVacuumCheck01

theorem originalFourRaiseCheck01 :
    ∀ T : Fin 24, ∀ r : OddMode 1, 1≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 1 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 1 (T.val+1) r.val.val) := by
  exact DegreeOneLadderBridgeCandidate.originalFourRaiseCheck01

#print axioms originalFourVacuumCheck01
#print axioms originalFourRaiseCheck01
end TorusLean.Shared.FermionLocalJet.FourCoupling
