import torus.shared.BosonFiniteCertificateCoordinate

/-!
# Canonical realization of a fixed planar relative form

For a concrete finite family in the existing `ThreeSector`, a form matrix E
is realized by the rank-one coefficient C with F C F = E, where F is the
actual canonical Gram matrix. In particular C = J E J when J is a verified
inverse of F. The resulting operator is zero on the orthogonal complement
of the family span. This constructs the fixed planar relative compression;
it does not identify it with a physical torus single-contraction operator.
-/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateRealization
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}

def familyGram (w : Fin r → ThreeSector ι) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ip (w i).val (w j).val

def familySynthesis (w : Fin r → ThreeSector ι) (x : Fin r → ℂ) : ThreeSector ι :=
  ∑ i, x i • w i

def familyAnalysis (w : Fin r → ThreeSector ι) (f : ThreeSector ι) : Fin r → ℂ :=
  fun i => ip (w i).val f.val

theorem familyGram_isHermitian (w : Fin r → ThreeSector ι) :
    (familyGram w).IsHermitian := by
  ext i j
  exact occupationInner_conj_symm (fun _ : ι => 1) (w j).val (w i).val

theorem familyAnalysis_synthesis (w : Fin r → ThreeSector ι) (x : Fin r → ℂ) :
    familyAnalysis w (familySynthesis w x) = familyGram w *ᵥ x := by
  funext i
  simp only [familyAnalysis, familySynthesis, Submodule.coe_sum, Submodule.coe_smul,
    inner_sum_right, TwoBodyLift.inner_smul_right, familyGram,
    Matrix.mulVec, dotProduct, mul_comm]

/-- Concrete relative vectors obtained from the paper occupation block have
exactly the rationally computable Gram `Uᴴ diag(g) U`. -/
theorem canonicalRelativeFamily_gram {B : Type*} [Fintype B] [DecidableEq B]
    (scale : ι → ℕ) (occ : B → (ι →₀ ℕ)) (hocc : Function.Injective occ)
    (hdegree : ∀ a, (occ a).degree = 3) (U : Matrix B (Fin r) ℂ) :
    familyGram (fun j => canonicalThreeBlock scale occ hdegree (fun a => U a j)) =
      Uᴴ * Matrix.diagonal (fun a => (occupationMetricWeight scale (occ a) : ℂ)) * U := by
  rw [Matrix.mul_assoc]
  ext i j
  change ip (canonicalThreeBlock scale occ hdegree (fun a => U a i)).val
    (canonicalThreeBlock scale occ hdegree (fun a => U a j)).val = _
  rw [canonicalThreeBlock_inner scale occ hocc]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual canonical rank-one map |w_i><w_j| on the frozen N=3 carrier. -/
def familyRank (w : Fin r → ThreeSector ι) (i j : Fin r) :
    ThreeSector ι →ₗ[ℂ] ThreeSector ι where
  toFun f := ip (w j).val f.val • w i
  map_add' f g := by
    simp only [Submodule.coe_add, ip, occupationInner_add_right, add_smul]
  map_smul' c f := by
    simp only [Submodule.coe_smul, ip, occupationInner_smul_right, smul_smul]
    rfl

/-- A concrete finite sum of canonical rank-one operators, rather than an
abstract space or an operator postulated to have the desired form. -/
def rankOneRealization (w : Fin r → ThreeSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) : ThreeSector ι →ₗ[ℂ] ThreeSector ι :=
  ∑ i, ∑ j, C i j • familyRank w i j

theorem rankOneRealization_inner (w : Fin r → ThreeSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) (f g : ThreeSector ι) :
    ip f.val (rankOneRealization w C g).val =
      star (familyAnalysis w f) ⬝ᵥ (C *ᵥ familyAnalysis w g) := by
  have hs (i : Fin r) : star (ip (w i).val f.val) = ip f.val (w i).val :=
    occupationInner_conj_symm (fun _ : ι => 1) _ _
  simp only [rankOneRealization, LinearMap.sum_apply, LinearMap.smul_apply,
    familyRank, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul, inner_sum_right,
    TwoBodyLift.inner_smul_right, familyAnalysis,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two Gram factors are essential because E is a form matrix in the
possibly nonorthonormal family, whereas C is a rank-one coefficient matrix. -/
theorem rankOneRealization_synthesis_form (w : Fin r → ThreeSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → ℂ) :
    ip (familySynthesis w x).val
      (rankOneRealization w C (familySynthesis w y)).val =
      star x ⬝ᵥ ((familyGram w * C * familyGram w) *ᵥ y) := by
  rw [rankOneRealization_inner, familyAnalysis_synthesis, familyAnalysis_synthesis]
  simp only [star_mulVec, (familyGram_isHermitian w).eq,
    dotProduct_mulVec, vecMul_vecMul]

theorem rankOneRealization_form_of_sandwich (w : Fin r → ThreeSector ι)
    (F C E : Matrix (Fin r) (Fin r) ℂ) (hF : familyGram w = F)
    (hE : F * C * F = E) (x y : Fin r → ℂ) :
    ip (familySynthesis w x).val
      (rankOneRealization w C (familySynthesis w y)).val =
      star x ⬝ᵥ (E *ᵥ y) := by
  rw [rankOneRealization_synthesis_form, hF, hE]

/-- Positivity is on all actual canonical three-particle vectors, including
those outside the finite family span. -/
theorem rankOneRealization_nonneg (w : Fin r → ThreeSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : C.PosSemidef) (f : ThreeSector ι) :
    0 ≤ (ip f.val (rankOneRealization w C f).val).re := by
  rw [rankOneRealization_inner]
  exact (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (familyAnalysis w f))).1

/-- The same actual N=3 realization uses the existing normalized lift at all N. -/
theorem rankOneRealization_lift_nonneg (w : Fin r → ThreeSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : C.PosSemidef) (f : Core ι ℂ) :
    0 ≤ (ip f (threeBodyLift (rankOneRealization w C) f)).re :=
  threeBodyLift_nonneg _ (rankOneRealization_nonneg w C hC) f

/-- An explicit inverse witness is used, not a noncomputable inverse algorithm. -/
def inverseGramCoefficient (J E : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := J * E * J

theorem inverseGramCoefficient_sandwich (F J E : Matrix (Fin r) (Fin r) ℂ)
    (hFJ : F * J = 1) (hJF : J * F = 1) :
    F * inverseGramCoefficient J E * F = E := by
  simp only [inverseGramCoefficient]
  calc
    F * (J * E * J) * F = (F * J) * E * (J * F) := by simp only [Matrix.mul_assoc]
    _ = E := by rw [hFJ, hJF, Matrix.one_mul, Matrix.mul_one]

/-- Positivity is the existing matrix congruence theorem. -/
theorem inverseGramCoefficient_posSemidef (J E : Matrix (Fin r) (Fin r) ℂ)
    (hJ : J.IsHermitian) (hE : E.PosSemidef) :
    (inverseGramCoefficient J E).PosSemidef := by
  simpa only [inverseGramCoefficient, hJ.eq] using hE.conjTranspose_mul_mul_same J

theorem inverseGramRealization_form (w : Fin r → ThreeSector ι)
    (F J E : Matrix (Fin r) (Fin r) ℂ) (hF : familyGram w = F)
    (hFJ : F * J = 1) (hJF : J * F = 1) (x y : Fin r → ℂ) :
    ip (familySynthesis w x).val
      (rankOneRealization w (inverseGramCoefficient J E) (familySynthesis w y)).val =
      star x ⬝ᵥ (E *ᵥ y) :=
  rankOneRealization_form_of_sandwich w F _ E hF
    (inverseGramCoefficient_sandwich F J E hFJ hJF) x y

theorem inverseGramRealization_lift_nonneg (w : Fin r → ThreeSector ι)
    (J E : Matrix (Fin r) (Fin r) ℂ) (hJ : J.IsHermitian) (hE : E.PosSemidef)
    (f : Core ι ℂ) :
    0 ≤ (ip f (threeBodyLift (rankOneRealization w (inverseGramCoefficient J E)) f)).re :=
  rankOneRealization_lift_nonneg w _ (inverseGramCoefficient_posSemidef J E hJ hE) f

#print axioms familyGram_isHermitian
#print axioms canonicalRelativeFamily_gram
#print axioms rankOneRealization_inner
#print axioms rankOneRealization_form_of_sandwich
#print axioms rankOneRealization_nonneg
#print axioms rankOneRealization_lift_nonneg
#print axioms inverseGramRealization_form
#print axioms inverseGramRealization_lift_nonneg
end TorusLean.Shared.BosonFiniteCertificateRealization
