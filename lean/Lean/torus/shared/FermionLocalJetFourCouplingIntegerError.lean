import torus.shared.FermionLocalJetFourCouplingSlaterGram
import torus.shared.FermionLocalJetFourCouplingRowMatrix

/-! Original E_D, decoded through the actual alpha and S45 definitions.
The only residual irrational factors are the two original copy factorial
roots. All seven rows, ordered entry pairs, negative signs and signed powers
remain. This is a source derivation, prior to any literal matrix acceptance. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open scoped BigOperators ComplexConjugate

def integerFourV (D T r p j k : ℕ) : ℤ :=
  if r≤j+k then integerS45Coefficient r (j+k) j *
    integerS45Coefficient (D-r) (T-r) p else 0

def alphaSExponent (rho : CertificateRow) (a : CertificateEntry rho)
    (T r k : ℕ) : ℤ :=
  ((certificateEntryData rho a).1:ℤ)+1-((certificateRowData rho).1:ℤ) -
    (((certificateEntryData rho a).2.1+k+T-r:ℕ):ℤ)

def integerFourRowEntry (D r s : ℕ) (rho : CertificateRow)
    (a b : CertificateEntry rho) : ℚ :=
  let p := (certificateEntryData rho a).1
  let j := (certificateEntryData rho a).2.1
  let q := (certificateEntryData rho b).1
  let l := (certificateEntryData rho b).2.1
  let t := (certificateRowData rho).1
  let i := certificateJetIndex rho a
  let k := certificateJetIndex rho b
  let T := certificateFourTotal rho a b
  if D≤T then
    ((certificateEntryData rho a).2.2:ℚ) *
      ((certificateEntryData rho b).2.2:ℚ) *
      (integerFourV D T r p j k:ℚ) * (integerFourV D T s q l i:ℚ) *
      (2:ℚ)^(1-2*(T:ℤ)+(p:ℤ)+(q:ℤ)-(t:ℤ)+((r+s)/2:ℕ)) *
      ((i.factorial:ℚ)*(k.factorial:ℚ)*(t.factorial:ℚ) /
        ((T-D).factorial:ℚ)) / 100000000000000
  else 0

def integerFourError (D r s : ℕ) : ℚ :=
  -(∑ rho : CertificateRow, ∑ a : CertificateEntry rho,
    ∑ b : CertificateEntry rho, integerFourRowEntry D r s rho a b)

def integerFourErrorMatrix (D : ℕ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  fun i j => integerFourError D (2*i.val+1) (2*j.val+1)

theorem certificateAlpha_integer_roots (rho : CertificateRow)
    (a : CertificateEntry rho) :
    (certificateAlpha rho a:ℂ) =
      ((certificateEntryData rho a).2.2:ℂ) / 10000000 *
      ((Real.sqrt (2:ℝ):ℂ)^(certificateEntryData rho a).1 *
        factorialRootNat (certificateRowData rho).1 *
        factorialRootNat (certificateJetIndex rho a)) /
      ((Real.sqrt (2:ℝ):ℂ)^(certificateRowData rho).1 *
        factorialRootNat (certificateEntryData rho a).1 *
        factorialRootNat (certificateEntryData rho a).2.1) := by
  have hp (n : ℕ) : Real.sqrt ((2:ℝ)^n)=(Real.sqrt (2:ℝ))^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity) _,ih,pow_succ]
  unfold certificateAlpha certificateScaleSq
  push_cast
  rw [Real.sqrt_div (by positivity) _,
    Real.sqrt_mul (by positivity) _,Real.sqrt_mul (by positivity) _,
    Real.sqrt_mul (by positivity) _,Real.sqrt_mul (by positivity) _,hp,hp]
  simp only [factorialRootNat,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_intCast]
  ring

/-- A single true signed alpha*S factor. Negative exponents are integer
powers, so no subtraction or low-index boundary is silently truncated. -/
theorem certificateAlpha_paperS45_integer_power (rho : CertificateRow)
    (a : CertificateEntry rho) (D T k : ℕ) (r : OddMode D)
    (hDT : D≤T)
    (hT : (certificateEntryData rho a).1+(certificateEntryData rho a).2.1+k=T) :
    (certificateAlpha rho a:ℂ) *
      paperS45 r.val.val D T (certificateEntryData rho a).1
        (certificateEntryData rho a).2.1 k =
      ((certificateEntryData rho a).2.2:ℂ) / 10000000 *
        (integerFourV D T r.val.val (certificateEntryData rho a).1
          (certificateEntryData rho a).2.1 k:ℂ) *
        copyInverseRoot D r *
        (factorialRootNat (certificateRowData rho).1 *
          factorialRootNat (certificateJetIndex rho a) * factorialRootNat k /
          factorialRootNat (T-D)) *
        (Real.sqrt (2:ℝ):ℂ)^(alphaSExponent rho a T r.val.val k) := by
  have hrD : r.val.val≤D := Nat.le_of_lt_succ r.val.isLt
  by_cases hr : r.val.val≤(certificateEntryData rho a).2.1+k
  · have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by norm_num
    have hp :
        (Real.sqrt (2:ℝ):ℂ)^(alphaSExponent rho a T r.val.val k) =
        (Real.sqrt (2:ℝ):ℂ)^((certificateEntryData rho a).1+1) /
          ((Real.sqrt (2:ℝ):ℂ)^(certificateRowData rho).1 *
            (Real.sqrt (2:ℝ):ℂ)^((certificateEntryData rho a).2.1+k+T-r.val.val)) := by
      simp only [alphaSExponent,zpow_sub₀ h2,zpow_add₀ h2,zpow_one,zpow_natCast,
        pow_succ]
      ring
    rw [certificateAlpha_integer_roots,
      paperS45_integer_roots _ _ _ _ _ _ hrD hDT hT hr,hp]
    simp only [integerFourV,if_pos hr,Int.cast_mul,copyInverseRoot]
    field_simp [factorialRootNat_ne_zero,h2] <;> ring
  · have hz : s45 r.val.val ((certificateEntryData rho a).2.1+k)
        (certificateEntryData rho a).2.1=0 :=
      s45_outside _ _ _ (Or.inl (by omega))
    simp [paperS45,hrD,hDT,hT,hz,integerFourV,hr]

/-- Exact product of the two ordered row factors, retaining every r,s cross
term. The sqrt(2) exponent sum is even because both relative labels are odd. -/
theorem certificateFour_ordered_rational (D : ℕ) (r s : OddMode D)
    (rho : CertificateRow) (a b : CertificateEntry rho) :
    (if D≤certificateFourTotal rho a b then
      (certificateAlpha rho a:ℂ)*(certificateAlpha rho b:ℂ) *
        paperS45 r.val.val D (certificateFourTotal rho a b)
          (certificateEntryData rho a).1 (certificateEntryData rho a).2.1
          (certificateJetIndex rho b) *
        paperS45 s.val.val D (certificateFourTotal rho a b)
          (certificateEntryData rho b).1 (certificateEntryData rho b).2.1
          (certificateJetIndex rho a)
    else 0) =
      copyInverseRoot D r * copyInverseRoot D s *
        (integerFourRowEntry D r.val.val s.val.val rho a b:ℂ) := by
  by_cases hDT : D≤certificateFourTotal rho a b
  · rw [if_pos hDT]
    have hTa : (certificateEntryData rho a).1+(certificateEntryData rho a).2.1+
        certificateJetIndex rho b=certificateFourTotal rho a b := rfl
    have hTb : (certificateEntryData rho b).1+(certificateEntryData rho b).2.1+
        certificateJetIndex rho a=certificateFourTotal rho a b :=
      certificateFourTotal_exchange rho b a
    rw [show (certificateAlpha rho a:ℂ)*(certificateAlpha rho b:ℂ) *
        paperS45 r.val.val D (certificateFourTotal rho a b)
          (certificateEntryData rho a).1 (certificateEntryData rho a).2.1
          (certificateJetIndex rho b) *
        paperS45 s.val.val D (certificateFourTotal rho a b)
          (certificateEntryData rho b).1 (certificateEntryData rho b).2.1
          (certificateJetIndex rho a) =
        ((certificateAlpha rho a:ℂ) *
          paperS45 r.val.val D (certificateFourTotal rho a b)
            (certificateEntryData rho a).1 (certificateEntryData rho a).2.1
            (certificateJetIndex rho b)) *
        ((certificateAlpha rho b:ℂ) *
          paperS45 s.val.val D (certificateFourTotal rho a b)
            (certificateEntryData rho b).1 (certificateEntryData rho b).2.1
            (certificateJetIndex rho a)) by ring,
      certificateAlpha_paperS45_integer_power rho a D _ _ r hDT hTa,
      certificateAlpha_paperS45_integer_power rho b D _ _ s hDT hTb]
    by_cases hr : r.val.val≤(certificateEntryData rho a).2.1+certificateJetIndex rho b
    · by_cases hs : s.val.val≤(certificateEntryData rho b).2.1+certificateJetIndex rho a
      · let e : ℤ := 1-2*(certificateFourTotal rho a b:ℤ)+
          ((certificateEntryData rho a).1:ℤ)+((certificateEntryData rho b).1:ℤ)-
          ((certificateRowData rho).1:ℤ)+((r.val.val+s.val.val)/2:ℕ)
        have hex : alphaSExponent rho a (certificateFourTotal rho a b) r.val.val
              (certificateJetIndex rho b) +
            alphaSExponent rho b (certificateFourTotal rho a b) s.val.val
              (certificateJetIndex rho a) = 2*e := by
          obtain ⟨ir,hir⟩ := r.property
          obtain ⟨is,his⟩ := s.property
          dsimp only [alphaSExponent,e]
          omega
        have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by norm_num
        have hp :
            (Real.sqrt (2:ℝ):ℂ)^(alphaSExponent rho a (certificateFourTotal rho a b)
                r.val.val (certificateJetIndex rho b)) *
              (Real.sqrt (2:ℝ):ℂ)^(alphaSExponent rho b (certificateFourTotal rho a b)
                s.val.val (certificateJetIndex rho a)) = (2:ℂ)^e := by
          rw [← zpow_add₀ h2,hex,zpow_mul]
          congr 1
          exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
        have hf (n : ℕ) : (factorialRootNat n)^2=(n.factorial:ℂ) := by
          unfold factorialRootNat
          exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial)
        simp only [integerFourRowEntry,if_pos hDT]
        push_cast
        have ht : ((10000000:ℂ)^2)=100000000000000 := by norm_num
        calc
          _ = copyInverseRoot D r * copyInverseRoot D s *
              (((certificateEntryData rho a).2.2:ℂ) *
                ((certificateEntryData rho b).2.2:ℂ) *
                (integerFourV D (certificateFourTotal rho a b) r.val.val
                  (certificateEntryData rho a).1 (certificateEntryData rho a).2.1
                  (certificateJetIndex rho b):ℂ) *
                (integerFourV D (certificateFourTotal rho a b) s.val.val
                  (certificateEntryData rho b).1 (certificateEntryData rho b).2.1
                  (certificateJetIndex rho a):ℂ) *
                (2:ℂ)^e *
                ((factorialRootNat (certificateJetIndex rho a))^2 *
                  (factorialRootNat (certificateJetIndex rho b))^2 *
                  (factorialRootNat (certificateRowData rho).1)^2 /
                  (factorialRootNat (certificateFourTotal rho a b-D))^2) /
                (10000000:ℂ)^2) := by
            rw [← hp]
            field_simp [factorialRootNat_ne_zero] <;> ring
          _ = _ := by
            simp only [hf,ht,e,Int.natCast_ediv,Int.natCast_add,Nat.cast_ofNat]
      · simp [integerFourV,hs,integerFourRowEntry,hDT]
    · simp [integerFourV,hr,integerFourRowEntry,hDT]
  · simp [integerFourRowEntry,hDT]

/-- Actual E_D equals the rationally decoded original ordered source, with
exactly the two factorial-root copy factors and the original negative sign. -/
theorem certificateFourMatrix_eq_integer_error (D : ℕ) (r s : OddMode D) :
    certificateFourMatrix D r.val.val s.val.val =
      copyInverseRoot D r * copyInverseRoot D s *
        (integerFourError D r.val.val s.val.val:ℂ) := by
  simp only [certificateFourMatrix,integerFourError,Rat.cast_neg,Rat.cast_sum,
    Finset.mul_sum,mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact certificateFour_ordered_rational D r s rho a b

theorem certificateFourMatrixFin_eq_integer_error (D : ℕ) :
    (fun i j : Fin ((D+1)/2) => certificateFourMatrix D (2*i.val+1) (2*j.val+1)) =
      originalCopyRootDiagonal D * (integerFourErrorMatrix D).map (Rat.castHom ℂ) *
        originalCopyRootDiagonal D := by
  ext i j
  simp only [originalCopyRootDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.map_apply,Rat.coe_castHom,integerFourErrorMatrix]
  have h := certificateFourMatrix_eq_integer_error D
    (originalCopyMode D i) (originalCopyMode D j)
  change certificateFourMatrix D (2*i.val+1) (2*j.val+1) =
    copyInverseRoot D (originalCopyMode D i) *
      copyInverseRoot D (originalCopyMode D j) *
        (integerFourError D (2*i.val+1) (2*j.val+1):ℂ) at h
  rw [h]
  ring

#print axioms certificateAlpha_integer_roots
#print axioms certificateAlpha_paperS45_integer_power
#print axioms certificateFour_ordered_rational
#print axioms certificateFourMatrix_eq_integer_error
#print axioms certificateFourMatrixFin_eq_integer_error
end TorusLean.Shared.FermionLocalJet.FourCoupling
