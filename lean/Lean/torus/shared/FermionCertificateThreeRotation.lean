import torus.shared.FermionLocalJetFourCouplingParity
import torus.shared.FermionCertificateThreeDecode
import Mathlib.Data.Matrix.Mul

/-! The full original a=2,b=1 pair/spectator coupling. This is a real
orbital unitary on the existing normalized two-mode coefficient space.
Its later exterior insertion is linear and may have a kernel. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.TwoBodyLift
open TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

def couplingU : ℂ := (Real.sqrt (3:ℝ):ℂ)⁻¹

def couplingV : ℂ := (Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ)⁻¹

theorem couplingUV_square : couplingU^2+couplingV^2=1 := by
  have h2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h3 : (Real.sqrt (3:ℝ):ℂ)^2=3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hn : (Real.sqrt (3:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)))
  unfold couplingU couplingV
  calc
    _ = (1+(Real.sqrt (2:ℝ):ℂ)^2)/(Real.sqrt (3:ℝ):ℂ)^2 := by
      field_simp
      <;> ring
    _ = 1 := by rw [h2,h3]; norm_num

private def rotationThreeLinear : Orbital (Fin 2) →ₗ[ℂ] Orbital (Fin 2) where
  toFun v := (couplingV*v 0+couplingU*v 1) • EuclideanSpace.single 0 1+
    (couplingU*v 0-couplingV*v 1) • EuclideanSpace.single 1 1
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

private theorem rotationThreeLinear_zero (v : Orbital (Fin 2)) :
    rotationThreeLinear v 0=couplingV*v 0+couplingU*v 1 := by
  simp [rotationThreeLinear]

private theorem rotationThreeLinear_one (v : Orbital (Fin 2)) :
    rotationThreeLinear v 1=couplingU*v 0-couplingV*v 1 := by
  simp [rotationThreeLinear]

private theorem rotationThreeLinear_involutive : Function.Involutive rotationThreeLinear := by
  intro v
  ext i
  fin_cases i
  · change rotationThreeLinear (rotationThreeLinear v) 0=v 0
    simp only [rotationThreeLinear_zero,rotationThreeLinear_one]
    calc
      _ = (couplingU^2+couplingV^2)*v 0 := by ring
      _ = _ := by rw [couplingUV_square,one_mul]
  · change rotationThreeLinear (rotationThreeLinear v) 1=v 1
    simp only [rotationThreeLinear_zero,rotationThreeLinear_one]
    calc
      _ = (couplingU^2+couplingV^2)*v 1 := by ring
      _ = _ := by rw [couplingUV_square,one_mul]

private def rotationThreeLinearEquiv : Orbital (Fin 2) ≃ₗ[ℂ] Orbital (Fin 2) :=
  { rotationThreeLinear with
    invFun := rotationThreeLinear
    left_inv := rotationThreeLinear_involutive
    right_inv := rotationThreeLinear_involutive }

private theorem rotationThreeLinear_inner (v w : Orbital (Fin 2)) :
    inner ℂ (rotationThreeLinear v) (rotationThreeLinear w)=inner ℂ v w := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,
    Pi.star_apply,rotationThreeLinear_zero,rotationThreeLinear_one,star_mul,star_add,star_sub]
  have hu : star couplingU=couplingU := by simp [couplingU,Complex.star_def]
  have hv : star couplingV=couplingV := by simp [couplingV,Complex.star_def]
  rw [hu,hv]
  calc
    _ = (couplingU^2+couplingV^2)*(star (v 0)*w 0+star (v 1)*w 1) := by ring
    _ = _ := by rw [couplingUV_square,one_mul]; ring

def rotationThree : Unitary (Fin 2) :=
  rotationThreeLinearEquiv.isometryOfInner rotationThreeLinear_inner

def rotateThreePolynomial : Core (Fin 2) ℂ →ₐ[ℂ] Core (Fin 2) ℂ :=
  secondQuantization rotationThree

theorem rotateThreePolynomial_X_zero :
    rotateThreePolynomial (MvPolynomial.X 0)=
      couplingV • MvPolynomial.X 0+couplingU • MvPolynomial.X 1 := by
  simp only [rotateThreePolynomial,secondQuantization,MvPolynomial.aeval_X,modeLinear,
    Fin.sum_univ_two,rotationThree,rotationThreeLinearEquiv]
  simp [rotationThreeLinear,MvPolynomial.smul_eq_C_mul] <;> ring

theorem rotateThreePolynomial_X_one :
    rotateThreePolynomial (MvPolynomial.X 1)=
      couplingU • MvPolynomial.X 0-couplingV • MvPolynomial.X 1 := by
  simp only [rotateThreePolynomial,secondQuantization,MvPolynomial.aeval_X,modeLinear,
    Fin.sum_univ_two,rotationThree,rotationThreeLinearEquiv]
  simp [rotationThreeLinear,MvPolynomial.smul_eq_C_mul] <;> ring

theorem rotateThreePolynomial_inner (f g : Core (Fin 2) ℂ) :
    ip (rotateThreePolynomial f) (rotateThreePolynomial g)=ip f g :=
  secondQuantization_inner rotationThree f g

theorem rotateThreePolynomial_homogeneous (T : ℕ) (f : Core (Fin 2) ℂ)
    (hf : f.IsHomogeneous T) : (rotateThreePolynomial f).IsHomogeneous T :=
  secondQuantization_sector rotationThree T f hf

private def reverseDegree (T : ℕ) (z : Fin (T+1)) : Fin (T+1) := ⟨T-z.val,by omega⟩

private theorem reverseDegree_injective (T : ℕ) : Function.Injective (reverseDegree T) := by
  intro z w h
  have hv := congrArg Fin.val h
  simp only [reverseDegree] at hv
  apply Fin.ext
  have hz := z.isLt
  have hw := w.isLt
  omega

/-- Relative degree z and COM degree T-z in the original normalized input. -/
def couplingPolynomialThree (T : ℕ) (z : Fin (T+1)) : Core (Fin 2) ℂ :=
  rotateThreePolynomial (canonicalWord T (reverseDegree T z))

def coefficientThree (T : ℕ) (z p : Fin (T+1)) : ℂ :=
  ip (canonicalWord T p) (couplingPolynomialThree T z)

theorem couplingPolynomialThree_homogeneous (T : ℕ) (z : Fin (T+1)) :
    (couplingPolynomialThree T z).IsHomogeneous T :=
  rotateThreePolynomial_homogeneous T _ (canonicalWord_homogeneous T _)

theorem coefficientThree_expansion (T : ℕ) (z : Fin (T+1)) :
    couplingPolynomialThree T z=∑ p : Fin (T+1), coefficientThree T z p • canonicalWord T p :=
  canonicalWord_expansion T _ (couplingPolynomialThree_homogeneous T z)

/-- Exact polynomial in eq:F-coupling at u=1/sqrt3, v=sqrt(2/3). -/
theorem couplingPolynomialThree_eq_paper (T : ℕ) (z : Fin (T+1)) :
    couplingPolynomialThree T z=
      (factorialRootNat z.val*factorialRootNat (T-z.val))⁻¹ •
        ((couplingU • MvPolynomial.X 0-couplingV • MvPolynomial.X 1)^z.val *
          (couplingV • MvPolynomial.X 0+couplingU • MvPolynomial.X 1)^(T-z.val)) := by
  have hz : z.val≤T := Nat.le_of_lt_succ z.isLt
  simp only [couplingPolynomialThree,canonicalWord,reverseDegree,Nat.sub_sub_self hz,
    normalizedSpectatorWord,map_smul,map_mul,map_pow,
    rotateThreePolynomial_X_zero,rotateThreePolynomial_X_one]
  simp only [mul_comm]

theorem coefficientThree_eq_coeff (T : ℕ) (z p : Fin (T+1)) :
    coefficientThree T z p=factorialRootNat p.val*factorialRootNat (T-p.val)*
      (couplingPolynomialThree T z).coeff (twoExponent p.val (T-p.val)) :=
  canonicalWord_inner_coeff T p _

theorem coefficientThree_star (T : ℕ) (z p : Fin (T+1)) :
    star (coefficientThree T z p)=coefficientThree T z p := by
  have hc : MvPolynomial.map (starRingEnd ℂ) (couplingPolynomialThree T z)=
      couplingPolynomialThree T z := by
    rw [couplingPolynomialThree_eq_paper]
    simp [MvPolynomial.smul_eq_C_mul,factorialRootNat,couplingU,couplingV,Complex.star_def]
  have h := congrArg (fun f : Core (Fin 2) ℂ => f.coeff (twoExponent p.val (T-p.val))) hc
  simp only [MvPolynomial.coeff_map] at h
  rw [coefficientThree_eq_coeff]
  simp only [star_mul,h]
  simp [factorialRootNat,Complex.star_def]
  rw [h]
  ring

theorem coefficientThree_rows_orthonormal (T : ℕ) (z w : Fin (T+1)) :
    (∑ p : Fin (T+1), star (coefficientThree T z p)*coefficientThree T w p)=
      if z=w then 1 else 0 := by
  have he := coefficientThree_expansion T z
  calc
    _ = ip (couplingPolynomialThree T z) (couplingPolynomialThree T w) := by
      conv_rhs => rw [he,inner_sum_left]
      simp only [TwoBodyLift.inner_smul_left,coefficientThree]
    _ = ip (canonicalWord T (reverseDegree T z)) (canonicalWord T (reverseDegree T w)) :=
      rotateThreePolynomial_inner _ _
    _ = _ := by
      rw [canonicalWord_orthonormal]
      simp only [(reverseDegree_injective T).eq_iff]

/-- Completeness in the full coefficient space, with no inverse exterior Gram. -/
theorem coefficientThree_columns (T : ℕ) (p q : Fin (T+1)) :
    (∑ z : Fin (T+1), coefficientThree T z p*coefficientThree T z q)=
      if p=q then 1 else 0 := by
  classical
  let M : Matrix (Fin (T+1)) (Fin (T+1)) ℂ := coefficientThree T
  have hM : M*M.transpose=1 := by
    ext z w
    change (∑ p : Fin (T+1), M z p*M w p)=if z=w then 1 else 0
    simpa only [M,coefficientThree_star] using coefficientThree_rows_orthonormal T z w
  have hMt : M.transpose*M=1 := mul_eq_one_comm.mp hM
  have he := congrFun (congrFun hMt p) q
  change (∑ z : Fin (T+1), M z p*M z q)=if p=q then 1 else 0 at he
  exact he

/-- Arbitrary linear insertion preserves the complete reconstruction even
when actual exterior images are dependent or zero. -/
theorem coefficientThree_reconstruct {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : ℕ) (a : Fin (T+1) → V) (p : Fin (T+1)) :
    (∑ z : Fin (T+1), coefficientThree T z p •
      (∑ q : Fin (T+1), coefficientThree T z q • a q))=a p := by
  classical
  simp only [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,coefficientThree_columns]
  simp

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
