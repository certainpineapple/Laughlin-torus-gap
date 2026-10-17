import torus.shared.BosonNatThreeMatrixLiftCongruence

/-! Exact cancellation of a genuine full source basis change, before any
parameter integration. Both inverse-Gram factors are retained. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeInverseGramTransport
open TorusLean.Boson TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRankCongruence
open TorusLean.Shared.BosonNatThreeMatrixLiftCongruence
open TorusLean.Shared.BosonNatThreeMatrixLift
open Matrix
open scoped BigOperators ComplexConjugate

theorem inverseGram_change_congruence {r : ℕ}
    (S T J M : Matrix (Fin r) (Fin r) ℂ) (hST : S*T=1) :
    S * ((T*J*Tᴴ)*(Sᴴ*M*S)*(T*J*Tᴴ)) * Sᴴ = J*M*J := by
  have hstar : Tᴴ*Sᴴ=1 := by rw [←Matrix.conjTranspose_mul,hST,Matrix.conjTranspose_one]
  calc
    _ = (S*T)*J*(Tᴴ*Sᴴ)*M*(S*T)*J*(Tᴴ*Sᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hST,hstar]; simp only [Matrix.one_mul,Matrix.mul_one]

/-- The actual charge-three lifted form is invariant under a verified
full source basis change with its dual Gram. No unitary condition on S. -/
theorem natMatrixLiftForm_inverseGram_change (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (S T J M : Matrix (Fin r) (Fin r) ℂ) (hST : S*T=1)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixLiftForm G theta (seedCombination p S) (seedCombination_particle p hp S)
      ((T*J*Tᴴ)*(Sᴴ*M*S)*(T*J*Tᴴ)) f =
    natMatrixLiftForm G theta p hp (J*M*J) f := by
  rw [natMatrixLiftForm_seedCombination,inverseGram_change_congruence S T J M hST]

end TorusLean.Shared.BosonNatThreeInverseGramTransport
