import torus.shared.BosonNatThreeInverseGramTransport
import torus.shared.BosonFiniteCertificateNatRelativeRankComparisonCore

/-! Actual factorial-scaled occupation columns and their complete COM change
are transported through the original annihilator, before cell integration. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCOMColumnTransport
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeRankCongruence
open TorusLean.Shared.BosonNatThreeInverseGramTransport
open Matrix
open scoped BigOperators ComplexConjugate

def natOccupationColumns {r : ℕ} (occ : Fin r → (Fin 9 →₀ ℕ)) : Fin r → Core ℕ ℂ :=
  fun i => MvPolynomial.rename Fin.val (canonicalMonomial (factorialScale 8) (occ i))

theorem natOccupationColumns_particle {r : ℕ} (occ : Fin r → (Fin 9 →₀ ℕ))
    (hN : ∀ i, (occ i).degree=3) (i : Fin r) :
    (natOccupationColumns occ i).IsHomogeneous 3 :=
  natFamilyOfFin9_particle (fun i => canonicalThreeMonomial (factorialScale 8) (occ i) (hN i)) i

theorem actual_COM_columns_eq_seedCombination {r : ℕ}
    (occ : Fin r → (Fin 9 →₀ ℕ)) (S : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j))) :
    w = seedCombination (natOccupationColumns occ) S := by
  funext j
  rw [hw j]
  simp only [canonicalBlock,map_sum,map_smul,seedCombination,natOccupationColumns]

/-- Complete complex cross form, including unequal relative labels, with both
true inverse-Gram factors. This is pointwise in the original cell parameter. -/
theorem actual_COM_inverseGram_rows {r : ℕ} (G : Geometry) (theta : Twist) (R : ℂ)
    (occ : Fin r → (Fin 9 →₀ ℕ)) (S T J M : Matrix (Fin r) (Fin r) ℂ)
    (hST : S*T=1) (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j)))
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, ((T*J*Tᴴ)*(Sᴴ*M*S)*(T*J*Tᴴ)) i j *
      ip (natThreeAnnihilator G theta R (w i) f)
        (natThreeAnnihilator G theta R (w j) g)) =
    ∑ i, ∑ j, (J*M*J) i j *
      ip
        (natThreeAnnihilator G theta R (natOccupationColumns occ i) f)
        (natThreeAnnihilator G theta R (natOccupationColumns occ j) g) := by
  rw [actual_COM_columns_eq_seedCombination occ S w hw,
    seedCombination_matrix_cross, inverseGram_change_congruence S T J M hST]

end TorusLean.Shared.BosonNatThreeCOMColumnTransport
