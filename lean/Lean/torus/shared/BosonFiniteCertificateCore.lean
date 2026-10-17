/- Small reusable certificate soundness steps. No torus inequality is an input.
   A rectangular kernel basis comes with an explicit identity decomposition,
   so neither a singular Gram matrix nor the full lowering kernel is discarded. -/
import RationalPSDCertificate
set_option autoImplicit false
open Matrix
namespace TorusLean.BosonFiniteCertificate

def delta : ℚ := 1 / 1000000
def alpha : ℚ := 1 - 30 * (5 / 9 : ℚ)^9 - 1 / 50

theorem kernel_from_split {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (U : Matrix (Fin n) (Fin r) ℚ)
    (P : Matrix (Fin r) (Fin n) ℚ) (C : Matrix (Fin n) (Fin m) ℚ)
    (hAU : A * U = 0) (hsplit : U * P + C * A = 1) (v : Fin n → ℚ) :
    A *ᵥ v = 0 ↔ ∃ x : Fin r → ℚ, U *ᵥ x = v := by
  constructor
  · intro hv
    refine ⟨P *ᵥ v, ?_⟩
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M *ᵥ v) hsplit
    simpa only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero, one_mulVec] using he
  · rintro ⟨x, rfl⟩
    rw [mulVec_mulVec, hAU, zero_mulVec]

theorem kernel_preserved_from_split {n r : ℕ}
    (H E : Matrix (Fin n) (Fin n) ℚ) (U : Matrix (Fin n) (Fin r) ℚ)
    (P : Matrix (Fin r) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (hsplit : U * P + C * H = 1) (hEU : E * U = 0)
    (v : Fin n → ℚ) (hv : H *ᵥ v = 0) : E *ᵥ v = 0 := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M *ᵥ v) hsplit
  have he' : U *ᵥ (P *ᵥ v) = v := by
    simpa only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero, one_mulVec] using he
  rw [← he', mulVec_mulVec, hEU, zero_mulVec]

#print axioms kernel_from_split
#print axioms kernel_preserved_from_split
end TorusLean.BosonFiniteCertificate
