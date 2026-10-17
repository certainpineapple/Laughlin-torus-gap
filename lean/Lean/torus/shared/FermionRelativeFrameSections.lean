import torus.shared.PhysicalFermionNormalSquarePositive
import torus.shared.RelativeJetMapKernel

/-!
The original m=1 CAR pair has charge-two coefficients only after its
antisymmetry is used.  These sections are constructed from the actual J₁
map and reproduce precisely the antisymmetrized original coefficients.
No individual non-holomorphic raw-jet product is declared to be an LLL.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.PhysicalFermionPairContraction TorusLean.Shared.PhysicalFermionPairLift
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.NormalJetBridge
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.PlaneJetReproducing
open scoped TensorProduct ComplexConjugate BigOperators

abbrev PairIndex (G : Geometry) (theta : Twist) :=
  PhysicalFermionNormalSquare.PairIndex (physicalQ G theta)

/-- True charge-two section with the original ordered-CAR factor one half. -/
def pairSection (G : Geometry) (theta : Twist) (p : PairIndex G theta) : LLL G theta 2 :=
  jetScale 1 1 1 • relativeJet G theta 1 1 1
    (orbitalBasis G theta (physicalIndexEquiv G theta p.1) ⊗ₜ[ℂ]
      orbitalBasis G theta (physicalIndexEquiv G theta p.2))

lemma relativeJet_m1_orbitals (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) :
    (relativeJet G theta 1 1 1
      (orbitalBasis G theta i ⊗ₜ[ℂ] orbitalBasis G theta j)).val R =
      pairM1 G theta i j R := by
  rw [relativeJet_apply]
  simp only [Nat.cast_one]
  have hf (z : ℂ × ℂ) :
      rawPairFunction G theta 1 1
        (orbitalBasis G theta i ⊗ₜ[ℂ] orbitalBasis G theta j) z =
      1 * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) *
        (orbitalFactor G theta i z.1 * orbitalFactor G theta j z.2) := by
    rw [rawPairFunction_tmul_apply, orbitalFactor_eq, orbitalFactor_eq]
    ring
  have hj := localNormalJet_gaussian_factor 1 1 (by norm_num) 1 _ _ 1 hf R
  trans (jetScale 1 1 1)⁻¹ * (1 * gaussianFactor (1+1) R) *
    iteratedDeriv 1 (fun r : ℂ =>
      orbitalFactor G theta i (jacobiFirst 1 1 R r) *
      orbitalFactor G theta j (jacobiSecond 1 1 R r)) 0
  · exact hj
  simp only [one_mul, iteratedDeriv_one]
  have heq : (fun r : ℂ => orbitalFactor G theta i (jacobiFirst 1 1 R r) *
      orbitalFactor G theta j (jacobiSecond 1 1 R r)) =
      (fun r : ℂ => orbitalFactor G theta i (R+r/2) *
        orbitalFactor G theta j (R-r/2)) := by
    funext r
    have h₁ : jacobiFirst 1 1 R r = R+r/2 := by norm_num [jacobiFirst] <;> ring
    have h₂ : jacobiSecond 1 1 R r = R-r/2 := by norm_num [jacobiSecond] <;> ring
    rw [h₁,h₂]
  rw [heq, normal_product_derivative]
  norm_num [pairM1]

/-- The normalization is inherited from the physical contact, not selected
by adjusting the four-body bound. -/
theorem pairSection_apply (G : Geometry) (theta : Twist)
    (p : PairIndex G theta) (R : ℂ) :
    (pairSection G theta p).val R =
      rawM1PairCoefficient G theta (physicalIndexEquiv G theta p.1)
        (physicalIndexEquiv G theta p.2) R / 2 := by
  change jetScale 1 1 1 *
    (relativeJet G theta 1 1 1
      (orbitalBasis G theta (physicalIndexEquiv G theta p.1) ⊗ₜ[ℂ]
        orbitalBasis G theta (physicalIndexEquiv G theta p.2))).val R = _
  rw [relativeJet_m1_orbitals, pairM1_eq_rawM1PairCoefficient]
  field_simp [jetScale_ne_zero 1 1 (by norm_num) (by norm_num) 1]

/-- Antisymmetrization cancels the unwanted conjugate-coordinate term. -/
theorem pairSection_apply_coefficient (G : Geometry) (theta : Twist)
    (p : PairIndex G theta) (R : ℂ) :
    (pairSection G theta p).val R =
      (jetPairCoefficient G theta p R - jetPairCoefficient G theta p.swap R) / 2 := by
  rw [pairSection_apply]
  simp only [rawM1PairCoefficient, physicalOrbitalCoordinates_basis, rawPairGram,
    rawGram_right_mode, jetPairCoefficient, Prod.fst_swap, Prod.snd_swap]
  ring

lemma modePairAnnihilate_swap (Q : ℕ)
    (p : PhysicalFermionNormalSquare.PairIndex Q) :
    modePairAnnihilate Q p.swap = -modePairAnnihilate Q p := by
  apply LinearMap.ext
  intro x
  exact vectorAnnihilate_anticomm_apply Q (mode p.1) (mode p.2) x

lemma swapped_coefficient_sum (G : Geometry) (theta : Twist) (R : ℂ) :
    (∑ p : PairIndex G theta, jetPairCoefficient G theta p.swap R •
      modePairAnnihilate (physicalQ G theta) p) =
      -(∑ p : PairIndex G theta, jetPairCoefficient G theta p R •
        modePairAnnihilate (physicalQ G theta) p) := by
  classical
  simp only [Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show modePairAnnihilate (physicalQ G theta) (j,i) =
      -modePairAnnihilate (physicalQ G theta) (i,j) from
      modePairAnnihilate_swap _ (i,j), smul_neg]

/-- Exact raw CAR expansion in genuine physical charge-two sections.
The CAR sign, the determinant factor one half, and the m=1 derivative
normalization have all been proved; no bosonic pair formula is reused. -/
theorem pairAt_section_expansion (G : Geometry) (theta : Twist) (R : ℂ) :
    pairAt G theta R = ∑ p : PairIndex G theta,
      (pairSection G theta p).val R • modePairAnnihilate (physicalQ G theta) p := by
  classical
  symm
  simp_rw [pairSection_apply_coefficient]
  calc
    _ = (2 : ℂ)⁻¹ •
        ((∑ p : PairIndex G theta, jetPairCoefficient G theta p R •
          modePairAnnihilate (physicalQ G theta) p) -
         (∑ p : PairIndex G theta, jetPairCoefficient G theta p.swap R •
          modePairAnnihilate (physicalQ G theta) p)) := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [smul_sub, smul_smul]
      module
    _ = _ := by
      rw [swapped_coefficient_sum, ← pairAt_expansion]
      module

#print axioms relativeJet_m1_orbitals
#print axioms pairSection_apply
#print axioms pairSection_apply_coefficient
#print axioms modePairAnnihilate_swap
#print axioms pairAt_section_expansion
end TorusLean.Shared.FermionRelativeFrame
