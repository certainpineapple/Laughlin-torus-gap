import torus.shared.BosonFiniteCertificateNatCutoffComparison
import torus.shared.BosonFiniteCertificateRealization

/-! Finite-family synthesis, analysis and rank forms in the genuine Nat
occupation core. The family index may be empty. The two Gram factors are
retained: a form matrix E gives rank coefficient J E J, not E. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

variable {r : ℕ}

def natFamilySynthesis (w : Fin r → Core ℕ ℂ) (x : Fin r → ℂ) : Core ℕ ℂ :=
  ∑ i, x i • w i

def natFamilyAnalysis (w : Fin r → Core ℕ ℂ) (f : Core ℕ ℂ) : Fin r → ℂ :=
  fun i => natOccupationInner (w i) f

def natFamilyGram (w : Fin r → Core ℕ ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => natOccupationInner (w i) (w j)

/-- A finite sum of actual Nat occupation rank cross forms. -/
def natFamilyRankForm (w : Fin r → Core ℕ ℂ)
    (C : Matrix (Fin r) (Fin r) ℂ) (f g : Core ℕ ℂ) : ℂ :=
  star (natFamilyAnalysis w f) ⬝ᵥ (C *ᵥ natFamilyAnalysis w g)

def natFamilyOfFin9 (w : Fin r → ThreeSector (Fin 9)) : Fin r → Core ℕ ℂ :=
  fun i => MvPolynomial.rename Fin.val (w i).val

/-- Every renamed canonical three-particle family is a genuine Nat N3 family. -/
theorem natFamilyOfFin9_particle (w : Fin r → ThreeSector (Fin 9)) (i : Fin r) :
    (natFamilyOfFin9 w i).IsHomogeneous 3 := by
  have h : (w i).val.IsHomogeneous 3 := (w i).property
  exact h.rename_isHomogeneous

theorem natFamilyGram_isHermitian (w : Fin r → Core ℕ ℂ) :
    (natFamilyGram w).IsHermitian := by
  ext i j
  exact natOccupationInner_conj_symm (w j) (w i)

theorem natFamilyAnalysis_synthesis (w : Fin r → Core ℕ ℂ) (x : Fin r → ℂ) :
    natFamilyAnalysis w (natFamilySynthesis w x) = natFamilyGram w *ᵥ x := by
  funext i
  simp only [natFamilyAnalysis, natFamilySynthesis, natOccupationInner_sum_right,
    natOccupationInner_smul_right, natFamilyGram, Matrix.mulVec, dotProduct, mul_comm]

theorem natFamilyRankForm_eq_sum (w : Fin r → Core ℕ ℂ)
    (C : Matrix (Fin r) (Fin r) ℂ) (f g : Core ℕ ℂ) :
    natFamilyRankForm w C f g =
      ∑ i, ∑ j, C i j * star (natOccupationInner (w i) f) *
        natOccupationInner (w j) g := by
  simp only [natFamilyRankForm, natFamilyAnalysis, Matrix.mulVec, dotProduct,
    Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem natFamilyRankForm_synthesis (w : Fin r → Core ℕ ℂ)
    (C : Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → ℂ) :
    natFamilyRankForm w C (natFamilySynthesis w x) (natFamilySynthesis w y) =
      star x ⬝ᵥ ((natFamilyGram w * C * natFamilyGram w) *ᵥ y) := by
  rw [natFamilyRankForm, natFamilyAnalysis_synthesis, natFamilyAnalysis_synthesis]
  simp only [star_mulVec, (natFamilyGram_isHermitian w).eq,
    dotProduct_mulVec, vecMul_vecMul]

theorem natFamilyRankForm_inverseGram (w : Fin r → Core ℕ ℂ)
    (F J E : Matrix (Fin r) (Fin r) ℂ) (hF : natFamilyGram w = F)
    (hFJ : F * J = 1) (hJF : J * F = 1) (x y : Fin r → ℂ) :
    natFamilyRankForm w (inverseGramCoefficient J E)
      (natFamilySynthesis w x) (natFamilySynthesis w y) = star x ⬝ᵥ (E *ᵥ y) := by
  rw [natFamilyRankForm_synthesis, hF,
    inverseGramCoefficient_sandwich F J E hFJ hJF]

theorem natFamilyRankForm_nonneg (w : Fin r → Core ℕ ℂ)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : C.PosSemidef) (f : Core ℕ ℂ) :
    0 ≤ (natFamilyRankForm w C f f).re :=
  (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (natFamilyAnalysis w f))).1

theorem natFamilySynthesis_rename (w : Fin r → ThreeSector (Fin 9)) (x : Fin r → ℂ) :
    natFamilySynthesis (natFamilyOfFin9 w) x =
      MvPolynomial.rename Fin.val (familySynthesis w x).val := by
  simp only [natFamilySynthesis, natFamilyOfFin9, familySynthesis,
    Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]

theorem natFamilyGram_rename (w : Fin r → ThreeSector (Fin 9)) :
    natFamilyGram (natFamilyOfFin9 w) = familyGram w := by
  ext i j
  exact natOccupationInner_rename_fin9 (w i).val (w j).val

/-- Column-family synthesis is the actual canonical block at B*x, including
when the relative family has dimension zero. -/
theorem canonicalFamilySynthesis_eq_block {B : Type*} [Fintype B] [DecidableEq B]
    (scale : Fin 9 → ℕ) (occ : B → (Fin 9 →₀ ℕ))
    (hdegree : ∀ a, (occ a).degree = 3) (U : Matrix B (Fin r) ℂ) (x : Fin r → ℂ) :
    (familySynthesis
      (fun j => canonicalThreeBlock scale occ hdegree (fun a => U a j)) x).val =
      canonicalBlock scale occ (U *ᵥ x) := by
  simp only [familySynthesis, Submodule.coe_sum, Submodule.coe_smul,
    canonicalThreeBlock_val, canonicalBlock, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]

#print axioms natFamilyOfFin9_particle
#print axioms natFamilyGram_isHermitian
#print axioms natFamilyAnalysis_synthesis
#print axioms natFamilyRankForm_eq_sum
#print axioms natFamilyRankForm_synthesis
#print axioms natFamilyRankForm_inverseGram
#print axioms natFamilyRankForm_nonneg
#print axioms natFamilySynthesis_rename
#print axioms natFamilyGram_rename
#print axioms canonicalFamilySynthesis_eq_block
end TorusLean.BosonFiniteCertificate
