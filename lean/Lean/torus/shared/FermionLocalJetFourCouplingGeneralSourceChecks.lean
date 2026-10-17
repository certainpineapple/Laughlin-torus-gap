import torus.shared.FermionLocalJetFourCouplingGeneralSourceCoefficientBridge
import torus.shared.FermionLocalJetFourCouplingGeneralSourceSymmetry

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. No vacuum/raising target is assumed. The bounded
wrappers retain every original condition and mode. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open GeneralSourcePolynomialCandidate GeneralSourceEncodingCandidate
open GeneralHalfSpaceCandidate GeneralSourceSymmetryCandidate
open DegreeOneLadderBridgeCandidate
namespace GeneralSourceChecksCandidate

theorem integerSourceWords_eq_orderedPairMask (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) :
    integerSourceWords D T r = orderedPairMask (factorialWeightedWords (fullSourcePolynomial D T r)) := by
  exact GeneralSourceCoefficientBridgeCandidate.integerSourceWords_eq_filter_factorialWeightedWords
    D T r hrD hDT

theorem original_source_alternate_four (D T r : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hr : Odd r) :
    alternateIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D T r)) =
      (4 : ℤ) • alternateIntegerFourWords (integerSourceWords D T r) := by
  rw [integerSourceWords_eq_orderedPairMask D T r hrD hDT]
  exact fullSourceWords_alternate_four_mask D T r hr

theorem four_smul_cancel (c d : IntegerFourWords) (h : (4 : ℤ) • c = (4 : ℤ) • d) : c=d := by
  ext w
  have hw := congrArg (fun f : IntegerFourWords => f w) h
  simp only [Finsupp.smul_apply,smul_eq_mul] at hw
  omega

/-- Original integer vacuum identity, now for every D and every odd mode. -/
theorem original_source_vacuum (D r : ℕ) (hrD : r≤D) (hr : Odd r) :
    alternateIntegerFourWords (lowerIntegerFourWords (integerSourceWords D D r))=0 := by
  apply four_smul_cancel
  calc
    (4 : ℤ) • alternateIntegerFourWords (lowerIntegerFourWords (integerSourceWords D D r)) =
        lowerIntegerFourWords ((4 : ℤ) • alternateIntegerFourWords (integerSourceWords D D r)) := by
      rw [map_smul,alternate_lower]
    _ = lowerIntegerFourWords
        (alternateIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D D r))) := by
      rw [← original_source_alternate_four D D r hrD le_rfl hr]
    _ = alternateIntegerFourWords
        (lowerIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D D r))) :=
      (alternate_lower _).symm
    _ = alternateIntegerFourWords
        (factorialWeightedWords (collectiveDerivative (fullSourcePolynomial D D r))) := by
      rw [factorialWeightedWords_lower]
    _ = (4 : ℤ) • (0 : IntegerFourWords) := by
      rw [fullSourcePolynomial_vacuum,map_zero,map_zero,smul_zero]

/-- Original full-T raising identity, without the unnecessary upper cutoff. -/
theorem original_source_raise (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) (hr : Odd r) :
    alternateIntegerFourWords (raiseIntegerFourWords (integerSourceWords D T r)) =
      alternateIntegerFourWords (integerSourceWords D (T+1) r) := by
  apply four_smul_cancel
  calc
    (4 : ℤ) • alternateIntegerFourWords (raiseIntegerFourWords (integerSourceWords D T r)) =
        raiseIntegerFourWords ((4 : ℤ) • alternateIntegerFourWords (integerSourceWords D T r)) := by
      rw [map_smul,alternate_raise]
    _ = raiseIntegerFourWords
        (alternateIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D T r))) := by
      rw [← original_source_alternate_four D T r hrD hDT hr]
    _ = alternateIntegerFourWords
        (raiseIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D T r))) :=
      (alternate_raise _).symm
    _ = alternateIntegerFourWords
        (factorialWeightedWords (collectiveSum*fullSourcePolynomial D T r)) := by
      rw [factorialWeightedWords_raise]
    _ = alternateIntegerFourWords
        (factorialWeightedWords (fullSourcePolynomial D (T+1) r)) := by
      rw [fullSourcePolynomial_raise D T r hDT]
    _ = (4 : ℤ) • alternateIntegerFourWords (integerSourceWords D (T+1) r) :=
      original_source_alternate_four D (T+1) r hrD (by omega) hr

/-- Exact shape of every original SourceChecksXX vacuum target. -/
theorem originalFourVacuumCheck (D : ℕ) :
    ∀ r : OddMode D, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords D D r.val.val)) = 0 := by
  intro r
  exact original_source_vacuum D r.val.val (Nat.le_of_lt_succ r.val.isLt) r.property

/-- Exact full mode and Fin 24 range shape of every original raising target. -/
theorem originalFourRaiseCheck (D : ℕ) :
    ∀ T : Fin 24, ∀ r : OddMode D, D≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords D T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords D (T.val+1) r.val.val) := by
  intro T r hDT hbound
  exact original_source_raise D T.val r.val.val (Nat.le_of_lt_succ r.val.isLt) hDT r.property

end GeneralSourceChecksCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.integerSourceWords_eq_orderedPairMask
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.original_source_alternate_four
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.four_smul_cancel
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.original_source_vacuum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.original_source_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.originalFourVacuumCheck
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceChecksCandidate.originalFourRaiseCheck
