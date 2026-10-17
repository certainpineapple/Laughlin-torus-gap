import torus.shared.BosonFiniteCertificateCanonicalZeroChannels
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate

/-- Every term acts on the actual input polynomial before taking its inner
product; there is no finite-matrix action in this definition. -/
def canonicalRowChannelForm {r : ℕ} (rows : Fin r → List ℤ) (t : ℕ)
    (f g : Core (Fin 9) ℂ) : ℂ :=
  ∑ i, (ip (canonicalFrozenRow9 t (rows i) f) (canonicalFrozenRow9 t (rows i) g) -
    ip (canonicalFrozenRow9 t [rowInteger (rows i) 0] f)
      (canonicalFrozenRow9 t [rowInteger (rows i) 0] g))

def canonicalOriginalM3Form (f g : Core (Fin 9) ℂ) : ℂ :=
  ∑ t : Fin 4, canonicalRowChannelForm
    (fun i : Fin (frozenRowCount t) => ((frozenRows t.val)[i.val]?.getD [])) t.val f g

theorem canonicalBlock_cross_form {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (A B : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ) (x y : Fin n → ℂ) :
    ip (A (canonicalBlock (factorialScale 8) occ x))
      (B (canonicalBlock (factorialScale 8) occ y)) =
      star x ⬝ᵥ ((fun a b =>
        ip (A (canonicalMonomial (factorialScale 8) (occ a)))
          (B (canonicalMonomial (factorialScale 8) (occ b)))) *ᵥ y) := by
  simp only [canonicalBlock, map_sum, map_smul, inner_sum_left, inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem canonicalRowChannelForm_block {n r : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (rows : Fin r → List ℤ) (t : ℕ) (x y : Fin n → ℂ) :
    canonicalRowChannelForm rows t (canonicalBlock (factorialScale 8) occ x)
      (canonicalBlock (factorialScale 8) occ y) =
      star x ⬝ᵥ (canonicalRowChannel occ rows t *ᵥ y) := by
  have hm : canonicalRowChannel occ rows t = ∑ i : Fin r,
      ((fun a b => ip (canonicalFrozenRow9 t (rows i)
        (canonicalMonomial (factorialScale 8) (occ a)))
        (canonicalFrozenRow9 t (rows i) (canonicalMonomial (factorialScale 8) (occ b)))) -
       (fun a b => ip (canonicalFrozenRow9 t [rowInteger (rows i) 0]
        (canonicalMonomial (factorialScale 8) (occ a)))
        (canonicalFrozenRow9 t [rowInteger (rows i) 0]
          (canonicalMonomial (factorialScale 8) (occ b))))) := by
    ext a b
    simp only [canonicalRowChannel, Finset.sum_apply, Pi.sub_apply]
  rw [hm, Matrix.sum_mulVec, dotProduct_sum]
  simp only [canonicalRowChannelForm, canonicalBlock_cross_form]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem canonicalOriginalM3Form_block {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (x y : Fin n → ℂ) :
    canonicalOriginalM3Form (canonicalBlock (factorialScale 8) occ x)
      (canonicalBlock (factorialScale 8) occ y) =
      star x ⬝ᵥ (canonicalAllRowChannels occ *ᵥ y) := by
  simp only [canonicalOriginalM3Form, canonicalAllRowChannels,
    canonicalRowChannelForm_block, Matrix.sum_mulVec, dotProduct_sum]

theorem matrixCross_congruence {n r : ℕ} (D : Matrix (Fin n) (Fin r) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin r → ℂ) :
    star (D *ᵥ x) ⬝ᵥ (M *ᵥ (D *ᵥ y)) = star x ⬝ᵥ ((Dᴴ * M * D) *ᵥ y) := by
  simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]

#print axioms canonicalBlock_cross_form
#print axioms canonicalRowChannelForm_block
#print axioms canonicalOriginalM3Form_block
#print axioms matrixCross_congruence
end TorusLean.BosonFiniteCertificate
