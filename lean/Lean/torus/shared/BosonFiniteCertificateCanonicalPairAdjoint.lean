import torus.shared.BosonFiniteCertificateConjugationPair
import torus.shared.BosonFiniteCertificateRescaleCCR

/-! Actual creator adjoints and Hamiltonian on the whole finite-variable core.
These definitions use the original conjugated differential pair operators;
no finite-block Riesz compression is used to define the Hamiltonian. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped ComplexConjugate BigOperators



def pairCoefficient9 (p a : ℕ) : ℂ :=
  (pairFactorialRoot9 (fin9 a) * pairFactorialRoot9 (fin9 (p-a)))⁻¹

theorem pairCoefficient9_real (p a : ℕ) : star (pairCoefficient9 p a) = pairCoefficient9 p a := by
  simp [pairCoefficient9, pairFactorialRoot9, Complex.star_def]

/-- True whole-core differential expansion of the existing conjugated pair. -/
theorem canonicalPair9_eq_differential (p : ℕ) :
    canonicalPair9 p = ((List.range (p+1)).map fun a =>
      pairCoefficient9 p a • (annihilate (fin9 (p-a))).comp (annihilate (fin9 a))).sum := by
  rw [canonicalPair9, finitePaperColumn9, conjugateOperator_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [List.map_cons, List.map_nil, normalWord_pair_remove,
    conjugateOperator_comp, conjugateOperator_annihilate,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  simp only [pairCoefficient9, mul_inv, mul_comm]

/-- Explicit creation polynomial with the same real coefficients, on all core. -/
def canonicalPairCreator9 (p : ℕ) : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  ((List.range (p+1)).map fun a =>
    pairCoefficient9 p a • (create (fin9 a)).comp (create (fin9 (p-a)))).sum

private theorem inner_list_sum_left {J : Type*} (l : List J)
    (f : J → Core (Fin 9) ℂ) (g : Core (Fin 9) ℂ) :
    ip ((l.map f).sum) g = (l.map fun a => ip (f a) g).sum := by
  induction l with
  | nil => simp [ip, occupationInner_zero_left]
  | cons a l ih => simp [ip, occupationInner_add_left, ih]

private theorem inner_list_sum_right {J : Type*} (l : List J)
    (f : Core (Fin 9) ℂ) (g : J → Core (Fin 9) ℂ) :
    ip f ((l.map g).sum) = (l.map fun a => ip f (g a)).sum := by
  induction l with
  | nil => simp [ip, occupationInner_zero_right]
  | cons a l ih => simp [ip, occupationInner_add_right, ih]

theorem linear_list_sum_apply {J : Type*} (l : List J)
    (F : J → Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ) (f : Core (Fin 9) ℂ) :
    (l.map F).sum f = (l.map fun a => F a f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Creator/annihilator adjointness is proved in the original factorial
occupation inner product, rather than postulated for a matrix compression. -/
theorem canonicalPairCreator9_adjoint (p : ℕ) (f g : Core (Fin 9) ℂ) :
    ip (canonicalPairCreator9 p f) g = ip f (canonicalPair9 p g) := by
  rw [canonicalPair9_eq_differential]
  simp only [canonicalPairCreator9, linear_list_sum_apply, inner_list_sum_left,
    inner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right, pairCoefficient9_real,
    ip, create_adjoint_canonical]

/-- The actual sum of pair B†B operators. Only p≤d enters; d≤8 will be imposed
when matching unaliased canonical degree blocks. -/
def canonicalPairHamiltonian9 (d : ℕ) : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  ((List.range (d+1)).map fun p =>
    ((p.factorial : ℂ) / (2 : ℂ)^(p+1)) •
      (canonicalPairCreator9 p).comp (canonicalPair9 p)).sum

theorem canonicalPairHamiltonian9_form (d : ℕ) (f g : Core (Fin 9) ℂ) :
    ip f (canonicalPairHamiltonian9 d g) =
      ((List.range (d+1)).map fun p =>
        ((p.factorial : ℂ) / (2 : ℂ)^(p+1)) *
          ip (canonicalPair9 p f) (canonicalPair9 p g)).sum := by
  simp only [canonicalPairHamiltonian9, linear_list_sum_apply, inner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, TwoBodyLift.inner_smul_right]
  congr 1
  have h := canonicalPairCreator9_adjoint p (canonicalPair9 p g) f
  have hh := congrArg star h
  simpa only [ip, occupationInner_conj_symm] using hh

end TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
