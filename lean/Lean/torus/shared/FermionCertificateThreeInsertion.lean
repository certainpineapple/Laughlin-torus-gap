import torus.shared.FermionCertificateThreeCoefficient
import torus.shared.ThermalCoherentFermionAnchoredJacobiAlgebra

/-! Full normalized pair/spectator coefficient space inserted into the
original Nat exterior algebra. The polynomial coordinate change is formal;
the actual v_p wedge e_j substitution is the genuine linear fermionMarkedW3,
never a commutative algebra evaluation in physical CAR generators. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open TorusLean.Shared.ThermalCoherentFermionAnchored
open scoped BigOperators

/-- X is the normalized pair oscillator A/sqrt2; Y is the spectator B. -/
def normalizedMarkedMap : Core (Fin 2) ℂ →ₐ[ℂ] FermionMarkedOscillator :=
  MvPolynomial.aeval ![(Real.sqrt (2:ℝ):ℂ)⁻¹ • markedPair,markedSpectator]

def threeInputInsertion : Core (Fin 2) ℂ →ₗ[ℂ] FormalExterior :=
  fermionMarkedW3.comp normalizedMarkedMap.toLinearMap

private theorem sqrt_nat_power (a : ℝ) (ha : 0≤a) (n : ℕ) :
    Real.sqrt (a^n)=(Real.sqrt a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg ha n),ih,pow_succ]

private theorem sqrt_power_factorial (a : ℝ) (ha : 0≤a) (n : ℕ) :
    Real.sqrt (a^n*(n.factorial:ℝ))=(Real.sqrt a)^n*Real.sqrt (n.factorial:ℝ) := by
  rw [Real.sqrt_mul (pow_nonneg ha n),sqrt_nat_power a ha n]

theorem normalizedMarkedMap_zero : normalizedMarkedMap (MvPolynomial.X 0)=
    (Real.sqrt (2:ℝ):ℂ)⁻¹ • markedPair := by simp [normalizedMarkedMap]

theorem normalizedMarkedMap_one : normalizedMarkedMap (MvPolynomial.X 1)=markedSpectator := by
  simp [normalizedMarkedMap]

/-- Every original normalized input, not only the two anchored columns. -/
theorem threeInputInsertion_canonical (T : ℕ) (p : Fin (T+1)) :
    threeInputInsertion (canonicalWord T p)=formalThreeSeed p.val (T-p.val) := by
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  have hf (n : ℕ) : (Real.sqrt (n.factorial:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<n.factorial)))
  simp only [threeInputInsertion,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    canonicalWord,normalizedSpectatorWord,map_smul,map_mul,map_pow,
    normalizedMarkedMap_zero,normalizedMarkedMap_one,smul_pow,smul_mul_assoc,
    fermionMarkedW3_pair_spectator,fermionMarkedBasisInsertion,smul_smul]
  rw [sqrt_power_factorial 2 (by norm_num)]
  simp only [factorialRootNat,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [show ((Real.sqrt (p.val.factorial:ℝ):ℂ)*(Real.sqrt ((T-p.val).factorial:ℝ):ℂ))⁻¹ *
      (((Real.sqrt (2:ℝ):ℂ)⁻¹)^p.val *
      (((Real.sqrt (2:ℝ):ℂ)^p.val*(Real.sqrt (p.val.factorial:ℝ):ℂ))*
        (Real.sqrt ((T-p.val).factorial:ℝ):ℂ)))=1 by
    field_simp [h2,hf] <;> simp [← mul_pow,h2]]
  exact one_smul _ _

private theorem uv_marked_relative :
    normalizedMarkedMap (couplingU • MvPolynomial.X 0-couplingV • MvPolynomial.X 1)=
      (Real.sqrt (6:ℝ):ℂ)⁻¹ • fermionMarkedRelative := by
  have h6 : (Real.sqrt (6:ℝ):ℂ)=(Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ) := by
    exact_mod_cast (show Real.sqrt (6:ℝ)=Real.sqrt (2:ℝ)*Real.sqrt (3:ℝ) by
      rw [show (6:ℝ)=2*3 by norm_num,Real.sqrt_mul (by norm_num)])
  have h2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  have hn3 : (Real.sqrt (3:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)))
  simp only [map_sub,map_smul,normalizedMarkedMap_zero,normalizedMarkedMap_one,
    couplingU,couplingV,fermionMarkedRelative,h6,smul_sub,smul_smul]
  have h : (Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ)⁻¹=
      ((Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ))⁻¹*2 := by
    calc
      _ = (Real.sqrt (2:ℝ):ℂ)^2 *
          ((Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ))⁻¹ := by
        field_simp [hn2,hn3]
        <;> ring
      _ = _ := by rw [h2]; ring
  rw [h]
  congr 1
  congr 1
  field_simp
  <;> ring

private theorem uv_marked_COM :
    normalizedMarkedMap (couplingV • MvPolynomial.X 0+couplingU • MvPolynomial.X 1)=
      (Real.sqrt (3:ℝ):ℂ)⁻¹ • fermionMarkedCOM := by
  have hn : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  simp only [map_add,map_smul,normalizedMarkedMap_zero,normalizedMarkedMap_one,
    couplingU,couplingV,fermionMarkedCOM,smul_add,smul_smul]
  congr 1
  congr 1
  field_simp
  <;> ring

/-- The complete rotated source is the previously defined true Jacobi column. -/
theorem threeInputInsertion_coupled (T : ℕ) (z : Fin (T+1)) :
    threeInputInsertion (couplingPolynomialThree T z)=formalJacobiColumn (T-z.val) z.val := by
  simp only [threeInputInsertion,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    couplingPolynomialThree_eq_paper,map_smul,map_mul,map_pow,
    uv_marked_relative,uv_marked_COM,smul_pow,smul_mul_smul_comm,smul_smul]
  rw [mul_comm (fermionMarkedRelative^z.val) (fermionMarkedCOM^(T-z.val))]
  unfold formalJacobiColumn
  rw [sqrt_power_factorial 3 (by norm_num),sqrt_power_factorial 6 (by norm_num)]
  simp only [factorialRootNat,Complex.ofReal_mul,Complex.ofReal_pow,mul_inv,inv_pow]
  congr 1
  ring

/-- All true v_p wedge e_(T-p) columns occur, with unchanged CAR relations. -/
theorem formalJacobiColumn_full_expansion (T : ℕ) (z : Fin (T+1)) :
    formalJacobiColumn (T-z.val) z.val=
      ∑ p : Fin (T+1), (sThree z.val T p.val:ℂ) • formalThreeSeed p.val (T-p.val) := by
  rw [← threeInputInsertion_coupled,coefficientThree_expansion,map_sum]
  simp only [map_smul,threeInputInsertion_canonical,coefficientThree_eq_sThree]

/-- Inverse full-source reconstruction is valid even when insertion has a kernel. -/
theorem formalThreeSeed_full_coupling (T : ℕ) (p : Fin (T+1)) :
    formalThreeSeed p.val (T-p.val)=
      ∑ z : Fin (T+1), (sThree z.val T p.val:ℂ) • formalJacobiColumn (T-z.val) z.val := by
  have h := coefficientThree_reconstruct T (fun p => formalThreeSeed p.val (T-p.val)) p
  simpa only [coefficientThree_eq_sThree,← formalJacobiColumn_full_expansion] using h.symm

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
