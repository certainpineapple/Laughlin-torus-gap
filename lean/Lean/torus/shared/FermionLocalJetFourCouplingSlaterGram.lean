import torus.shared.FermionLocalJetFourCouplingSlaterPresentation
import OAI.Analysis.Laughlin.FourBody.Matrix

/-! The actual Slater matrix has exactly the manuscript Gram, with both
factorial-root copy factors. Zero/repeated copy columns are retained. The
proof uses the original L and Z definitions, not a supplied Gram premise. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate Matrix
open scoped BigOperators ComplexConjugate

 theorem copyInverseRoot_star (D : ℕ) (r : OddMode D) :
    star (copyInverseRoot D r) = copyInverseRoot D r := by
  simp only [copyInverseRoot,factorialRootNat,Complex.star_def,
    map_inv₀,map_mul,Complex.conj_ofReal]

 theorem slaterRoot_star (D : ℕ) (A : SlaterIndex D) :
    star (slaterRoot D A) = slaterRoot D A := by
  simp only [slaterRoot,map_prod,factorialRootNat,Complex.star_def,Complex.conj_ofReal]

 theorem slaterRoot_ne_zero (D : ℕ) (A : SlaterIndex D) : slaterRoot D A≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => factorialRootNat_ne_zero _)

 theorem slaterRoot_sq (D : ℕ) (A : SlaterIndex D) :
    (slaterRoot D A)^2 =
      ((slaterTuple D A).1.factorial:ℂ) * ((slaterTuple D A).2.1.factorial:ℂ) *
      ((slaterTuple D A).2.2.1.factorial:ℂ) * ((slaterTuple D A).2.2.2.factorial:ℂ) := by
  have hs (n : ℕ) : (factorialRootNat n)^2=(n.factorial:ℂ) := by
    unfold factorialRootNat
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial)
  have htailj : Matrix.vecHead (Matrix.vecTail ![(slaterTuple D A).2.1,
      (slaterTuple D A).2.2.1,(slaterTuple D A).2.2.2]) =
      (slaterTuple D A).2.2.1 := rfl
  have htailk : Matrix.vecHead (Matrix.vecTail (Matrix.vecTail
      ![(slaterTuple D A).2.1,(slaterTuple D A).2.2.1,(slaterTuple D A).2.2.2])) =
      (slaterTuple D A).2.2.2 := rfl
  simp only [slaterRoot,Fin.prod_univ_four,slaterLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,htailj,htailk,mul_pow,hs]

 theorem originalSlaterMatrix_gram_entry (D : ℕ) (r s : OddMode D) :
    ((originalSlaterMatrix D)ᴴ * originalSlaterMatrix D) r s =
      copyInverseRoot D r * copyInverseRoot D s *
        (OAI.Laughlin.Certificate.Z D r.val.val s.val.val:ℂ) := by
  classical
  have hcopy (u : OddMode D) :
      (starRingEnd ℂ) (copyInverseRoot D u) = copyInverseRoot D u := by
    simpa only [Complex.star_def] using copyInverseRoot_star D u
  have hslater (A : SlaterIndex D) :
      (starRingEnd ℂ) (slaterRoot D A) = slaterRoot D A := by
    simpa only [Complex.star_def] using slaterRoot_star D A
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,originalSlaterMatrix,
    Complex.star_def,map_div₀,map_mul,hcopy,hslater,map_ratCast]
  have he (A : SlaterIndex D) :
      (copyInverseRoot D r * (OAI.Laughlin.Certificate.L D r.val.val (slaterTuple D A):ℂ) /
        slaterRoot D A) *
      (copyInverseRoot D s * (OAI.Laughlin.Certificate.L D s.val.val (slaterTuple D A):ℂ) /
        slaterRoot D A) =
      copyInverseRoot D r * copyInverseRoot D s *
        (OAI.Laughlin.Certificate.L D r.val.val (slaterTuple D A) *
          OAI.Laughlin.Certificate.L D s.val.val (slaterTuple D A) /
          (((slaterTuple D A).1.factorial:ℚ) * ((slaterTuple D A).2.1.factorial:ℚ) *
            ((slaterTuple D A).2.2.1.factorial:ℚ) *
            ((slaterTuple D A).2.2.2.factorial:ℚ)):ℚ) := by
    push_cast
    rw [← slaterRoot_sq]
    field_simp [slaterRoot_ne_zero] <;> ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Rat.cast_sum]
  apply congrArg (fun q : ℚ => (q : ℂ))
  rw [slaterIndex_sum D
    (fun A : ℕ × ℕ × ℕ × ℕ =>
      OAI.Laughlin.Certificate.L D r.val.val A *
        OAI.Laughlin.Certificate.L D s.val.val A /
          ((A.1.factorial:ℚ) * (A.2.1.factorial:ℚ) *
            (A.2.2.1.factorial:ℚ) * (A.2.2.2.factorial:ℚ)))]
  rfl

/-- Every original odd label occurs exactly once, including source-kernel
columns. This is only the explicit copy-index identification. -/
def originalCopyMode (D : ℕ) (i : Fin ((D+1)/2)) : OddMode D :=
  ⟨⟨2*i.val+1,by have hi := i.isLt; omega⟩,⟨i.val,rfl⟩⟩

def originalCopyIndex (D : ℕ) (r : OddMode D) : Fin ((D+1)/2) :=
  ⟨r.val.val/2,by
    have hr := r.val.isLt
    obtain ⟨k,hk⟩ := r.property
    omega⟩

 theorem originalCopyMode_index (D : ℕ) (r : OddMode D) :
    originalCopyMode D (originalCopyIndex D r)=r := by
  apply Subtype.ext
  apply Fin.ext
  obtain ⟨k,hk⟩ := r.property
  change 2*(r.val.val/2)+1=r.val.val
  omega

 theorem originalCopyIndex_mode (D : ℕ) (i : Fin ((D+1)/2)) :
    originalCopyIndex D (originalCopyMode D i)=i := by
  apply Fin.ext
  change (2*i.val+1)/2=i.val
  omega

 def originalCopyEquiv (D : ℕ) : Fin ((D+1)/2) ≃ OddMode D :=
  ⟨originalCopyMode D,originalCopyIndex D,originalCopyIndex_mode D,
    originalCopyMode_index D⟩

 def originalSlaterMatrixFin (D : ℕ) :
    Matrix (SlaterIndex D) (Fin ((D+1)/2)) ℂ :=
  fun A i => originalSlaterMatrix D A (originalCopyMode D i)

 def originalCopyRootDiagonal (D : ℕ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ :=
  Matrix.diagonal (fun i => copyInverseRoot D (originalCopyMode D i))

 theorem originalSlaterMatrix_gram (D : ℕ) :
    (originalSlaterMatrixFin D)ᴴ * originalSlaterMatrixFin D =
      originalCopyRootDiagonal D *
        (OAI.Laughlin.Certificate.gramRational D).map (Rat.castHom ℂ) *
        originalCopyRootDiagonal D := by
  ext i j
  change ((originalSlaterMatrix D)ᴴ * originalSlaterMatrix D)
    (originalCopyMode D i) (originalCopyMode D j) = _
  rw [originalSlaterMatrix_gram_entry]
  simp only [originalCopyRootDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.map_apply,OAI.Laughlin.Certificate.gramRational,
    OAI.Laughlin.Certificate.copyLabel,originalCopyMode,Rat.coe_castHom]
  ring

 theorem originalCopyRootDiagonal_sq (D : ℕ) :
    originalCopyRootDiagonal D * originalCopyRootDiagonal D =
      (Matrix.diagonal (OAI.Laughlin.Certificate.copyWeight D)).map (Rat.castHom ℂ) := by
  ext i j
  by_cases hij : i=j
  · subst j
    have hs (n : ℕ) : (factorialRootNat n)^2=(n.factorial:ℂ) := by
      unfold factorialRootNat
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial)
    simp only [originalCopyRootDiagonal,Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq,Matrix.map_apply,copyInverseRoot,originalCopyMode,
      OAI.Laughlin.Certificate.copyWeight,OAI.Laughlin.Certificate.copyLabel,Rat.coe_castHom]
    push_cast
    simp only [← pow_two,inv_pow,mul_pow,hs,one_div]
  · simp [originalCopyRootDiagonal,Matrix.diagonal_mul_diagonal,Matrix.map_apply,hij]

#print axioms copyInverseRoot_star
#print axioms slaterRoot_star
#print axioms slaterRoot_ne_zero
#print axioms slaterRoot_sq
#print axioms originalSlaterMatrix_gram_entry
#print axioms originalCopyMode_index
#print axioms originalCopyIndex_mode
#print axioms originalSlaterMatrix_gram
#print axioms originalCopyRootDiagonal_sq
end TorusLean.Shared.FermionLocalJet.FourCoupling
