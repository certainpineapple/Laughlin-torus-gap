import torus.shared.BosonFiniteCertificateNatFourCOMForm
import torus.shared.BosonFiniteCertificateNatCOMParticle
import torus.shared.BosonFiniteCertificateNatCOMOccupationAdjoint

/-! Actual charge-four COM normalization. The finite trace coefficient is
exactly (2/4) times the normalized-descendant cross form. The vacuum cross
normalization is proved using the true Nat adjoint and oscillator algebra. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson

theorem natFour_COM_iterate_inner (n : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hLg : canonicalCOMLowerNat g=0) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g) =
      ((4 : ℂ)^n*(n.factorial : ℂ))*natOccupationInner f g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',canonicalCOMRaiseNat_adjoint]
    rw [canonicalCOMNat_lower_iterate_particle 4 n g hNg hLg,
      natOccupationInner_smul_right,ih]
    simp only [Nat.cast_ofNat,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

/-- 1/sqrt(4^n n!) in an exact factorial-root expression. -/
def natFourCOMNormalization (n : ℕ) : ℂ :=
  (factorialRootNat n*(2 : ℂ)^n)⁻¹

theorem natFourCOMNormalization_star_mul (n : ℕ) :
    star (natFourCOMNormalization n)*natFourCOMNormalization n =
      ((4 : ℂ)^n*(n.factorial : ℂ))⁻¹ := by
  have h : star (factorialRootNat n*(2 : ℂ)^n)*(factorialRootNat n*(2 : ℂ)^n) =
      (4 : ℂ)^n*(n.factorial : ℂ) := by
    simp only [star_mul,star_pow,show star (2 : ℂ)=2 by norm_num]
    calc
      _ = (star (factorialRootNat n)*factorialRootNat n)*((2 : ℂ)^n*2^n) := by ring
      _ = (4 : ℂ)^n*(n.factorial : ℂ) := by
        rw [factorialRootNat_star_mul,← mul_pow]
        norm_num [mul_comm]
  simp only [natFourCOMNormalization,star_inv₀,← mul_inv,h]

def natFourNormalizedCOMDescendant (n : ℕ) (f : Core ℕ ℂ) : Core ℕ ℂ :=
  natFourCOMNormalization n • ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)

theorem natFourNormalizedCOMDescendant_inner (n : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hLg : canonicalCOMLowerNat g=0) :
    natOccupationInner (natFourNormalizedCOMDescendant n f)
      (natFourNormalizedCOMDescendant n g)=natOccupationInner f g := by
  rw [natFourNormalizedCOMDescendant,natFourNormalizedCOMDescendant,
    natOccupationInner_smul_left,natOccupationInner_smul_right,
    natFour_COM_iterate_inner n f g hNg hLg]
  rw [← mul_assoc (star (natFourCOMNormalization n)) (natFourCOMNormalization n),
    natFourCOMNormalization_star_mul]
  have hn : (4 : ℂ)^n*(n.factorial : ℂ) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero n (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem natFourOriginalCOMWeight_normalized (n : ℕ) :
    (natFourOriginalCOMWeight n : ℂ) =
      (1/2 : ℂ)*(star (natFourCOMNormalization n)*natFourCOMNormalization n) := by
  rw [natFourCOMNormalization_star_mul]
  simp only [natFourOriginalCOMWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast,pow_succ]
  have ha : (4 : ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  have hb : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [ha,hb]
  ring

private theorem natFour_scaled_operator_inner (O : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (c : ℂ) (f g : Core ℕ ℂ) :
    natOccupationInner (c • f) (O (c • g))=
      (star c*c)*natOccupationInner f (O g) := by
  rw [map_smul,natOccupationInner_smul_left,natOccupationInner_smul_right]
  ring

private theorem natFour_operator_COM_normalized (O : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (n : ℕ) (f g : Core ℕ ℂ) :
    (natFourOriginalCOMWeight n : ℂ)*
      natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
        (O ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g)) = (1/2 : ℂ)*
      natOccupationInner (natFourNormalizedCOMDescendant n f)
        (O (natFourNormalizedCOMDescendant n g)) := by
  rw [natFourOriginalCOMWeight_normalized]
  simp only [natFourNormalizedCOMDescendant,natFour_scaled_operator_inner]
  ring

/-- The original 2/4 COM factor is preserved exactly. The equality is about
actual normalized source descendants and actual M4, independent of tables. -/
theorem natFourOriginalCOMTerm_normalized (n : ℕ) (f g : Core ℕ ℂ) :
    natFourOriginalCOMTerm f g n = (1/2 : ℂ)*
      natOccupationInner (natFourNormalizedCOMDescendant n f)
        (canonicalNatFourOriginalOperator (natFourNormalizedCOMDescendant n g)) :=
  natFour_operator_COM_normalized canonicalNatFourOriginalOperator n f g

#print axioms natFour_COM_iterate_inner
#print axioms natFourCOMNormalization_star_mul
#print axioms natFourNormalizedCOMDescendant_inner
#print axioms natFourOriginalCOMWeight_normalized
#print axioms natFourOriginalCOMTerm_normalized
end TorusLean.BosonFiniteCertificate
